// macdesync — локальный SOCKS5-прокси для macOS: перед настоящим TLS ClientHello
// вбрасывает в то же TCP-соединение фейковый (с безобидным SNI), затем шлёт настоящий,
// разрезав его посередине SNI. Аналог связки zapret "fake,split2", но без NFQUEUE:
// номера seq/ack подсматриваются из SYN-ACK через BPF, фейк уходит через pcap_inject.
//
// сборка: DEVELOPER_DIR=/Library/Developer/CommandLineTools cc -O2 -Wall -o desync desync.c -lpcap
// запуск: sudo ./desync [-i en0] [-p 1080] [-s www.google.com] [-f md5sig,tlsrec] [-r 1] [-u 6] [-v]
//         -u N — сколько пустышек слать перед первым UDP-пакетом на новый адрес (голос Discord)
//         системный режим (все приложения, включая UDP): sing-box с tun.json поверх этого прокси
// тест:   ./desync -T
//
// Стратегия — слова через запятую. Задаётся ключом -f, а для отдельного соединения —
// логином SOCKS5 (curl --socks5-hostname 127.0.0.1:1080 --proxy-user 'md5sig,tlsrec:x' ...).
//   Как сделать, чтобы сервер фейк НЕ принял:
//     md5sig      TCP-опция MD5 (Linux-серверы молча отбрасывают)
//     badseq      seq вне окна
//     badsum      битая контрольная сумма TCP (домашний NAT может срезать)
//     ttl=N       фиксированный TTL (фейк должен дойти до DPI и умереть до сервера)
//     autottl=D   TTL = (хопы до сервера по SYN-ACK) - D, в пределах 3..20
//   Как выглядит фейк:
//     nofake      не слать фейк вовсе
//     tsopt       добавить TCP timestamp, как у настоящих сегментов
//     pad517      добить фейк до 517 байт, как у браузеров
//     sni=host    SNI фейка;  rep=N  сколько раз послать
//   Как уходит настоящий ClientHello:
//     pos=N       резать TCP на N-м байте (по умолчанию — посередине SNI)
//     tlsrec      разбить ещё и на две TLS-записи в той же точке
//     disorder    первый кусок послать с TTL=1, чтобы второй дошёл раньше (ценой одного RTO)
//
// ponytail: только IPv4, только TCP/TLS, только Ethernet/Wi-Fi (не utun). QUIC не трогаем —
// браузеры через SOCKS его и так не используют. IPv6/HTTP добавлять, когда упрёмся.
// ponytail: слова стратегии ищутся через strstr — хватает, пока имена не пересекаются.

#include <arpa/inet.h>
#include <assert.h>
#include <net/if.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pcap.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

static pcap_t *pc;
static const char *fake_sni = "www.google.com", *fool = "md5sig,tlsrec";
static int repeats = 1, verbose, ufakes = 6;
static unsigned ifidx;

// Слот на каждый локальный порт: поток соединения ждёт, поток pcap заполняет из SYN-ACK.
struct slot {
    uint8_t state;            // 0 свободен, 1 ждём SYN-ACK, 2 готов
    uint8_t eth[14], ttl;     // готовый Ethernet-заголовок для ответа; TTL из SYN-ACK
    uint8_t has_ts;
    uint32_t saddr, daddr;    // наш адрес / адрес сервера, сетевой порядок байт
    uint32_t seq, ack;        // чем должен быть помечен наш первый сегмент с данными
    uint32_t ts_val, ts_ecr;  // timestamp сервера и эхо нашего SYN
    uint64_t t0;              // мс в момент отправки SYN — чтобы продолжить наш timestamp
    uint16_t dport;
};
static struct slot slots[65536];
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cv = PTHREAD_COND_INITIALIZER;

#define P16(p, v) (*(p)++ = (uint8_t)((v) >> 8), *(p)++ = (uint8_t)(v))
static uint32_t rd32(const uint8_t *p) { return (uint32_t)p[0] << 24 | p[1] << 16 | p[2] << 8 | p[3]; }
static void wr32(uint8_t *p, uint32_t v) { p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v; }
static uint64_t now_ms(void) {
    struct timeval t;
    gettimeofday(&t, 0);
    return (uint64_t)t.tv_sec * 1000 + t.tv_usec / 1000;
}

static uint16_t csum(const uint8_t *p, int n, uint32_t s) {
    for (; n > 1; p += 2, n -= 2) s += p[0] << 8 | p[1];
    if (n) s += p[0] << 8;
    while (s >> 16) s = (s & 0xffff) + (s >> 16);
    return ~s;
}

// Смещение имени хоста внутри TLS ClientHello (длина в *len); -1, если это не ClientHello с SNI.
static int find_sni(const uint8_t *b, int n, int *len) {
    if (n < 44 || b[0] != 0x16 || b[5] != 1) return -1;
    int i = 43;                                   // запись 5 + handshake 4 + версия 2 + random 32
    i += 1 + b[i];                                // session id
    if (i + 2 > n) return -1;
    i += 2 + (b[i] << 8 | b[i + 1]);              // cipher suites
    if (i + 1 > n) return -1;
    i += 1 + b[i];                                // compression
    if (i + 2 > n) return -1;
    int end = i + 2 + (b[i] << 8 | b[i + 1]);
    if (end > n) end = n;                         // hello может не влезть в первый read
    for (i += 2; i + 4 <= end;) {
        int type = b[i] << 8 | b[i + 1], l = b[i + 2] << 8 | b[i + 3];
        i += 4;
        if (type == 0) {
            if (i + 5 > end) return -1;
            *len = b[i + 3] << 8 | b[i + 4];
            return i + 5 + *len <= end ? i + 5 : -1;
        }
        i += l;
    }
    return -1;
}

// Собирает минимальный правдоподобный ClientHello с заданным SNI. Возвращает длину (<= 520).
static int mk_hello(uint8_t *b, const char *sni, int pad) {
    static const uint8_t suites[] = {0, 6, 0x13, 1, 0x13, 2, 0x13, 3, 1, 0};   // 3 набора + null-сжатие
    static const uint8_t tail[] = {
        0, 0x0a, 0, 4, 0, 2, 0, 0x1d,                                          // supported_groups: x25519
        0, 0x0d, 0, 8, 0, 6, 4, 3, 8, 4, 4, 1,                                 // signature_algorithms
        0, 0x10, 0, 0x0e, 0, 0x0c, 2, 'h', '2', 8, 'h', 't', 't', 'p', '/', '1', '.', '1',   // ALPN
        0, 0x2b, 0, 3, 2, 3, 4,                                                // supported_versions: 1.3
        0, 0x33, 0, 0x26, 0, 0x24, 0, 0x1d, 0, 0x20};                          // key_share x25519 + 32 байта
    int n = (int)strlen(sni);
    uint8_t *p = b + 9;
    *p++ = 3, *p++ = 3;
    arc4random_buf(p, 32), p += 32;
    *p++ = 32, arc4random_buf(p, 32), p += 32;
    memcpy(p, suites, sizeof suites), p += sizeof suites;
    uint8_t *ext = p;
    p += 2;
    P16(p, 0), P16(p, n + 5), P16(p, n + 3), *p++ = 0, P16(p, n);
    memcpy(p, sni, n), p += n;
    memcpy(p, tail, sizeof tail), p += sizeof tail;
    arc4random_buf(p, 32), p += 32;
    if (pad && p - b + 4 < 517) {                                              // расширение padding (21)
        int l = 517 - (int)(p - b) - 4;
        P16(p, 21), P16(p, l), memset(p, 0, l), p += l;
    }
    int total = (int)(p - b);
    b[0] = 0x16, b[1] = 3, b[2] = 1, b[3] = (total - 5) >> 8, b[4] = total - 5;
    b[5] = 1, b[6] = 0, b[7] = (total - 9) >> 8, b[8] = total - 9;
    ext[0] = (p - ext - 2) >> 8, ext[1] = p - ext - 2;
    return total;
}

// Собирает кадр Ethernet+IP+TCP с фейковым ClientHello (буфер >= 1024). Возвращает длину кадра.
static int mk_fake(uint8_t *pk, const struct slot *s, uint16_t lport, const char *st, int *ttl_out) {
    uint8_t *ip = pk + 14, *tcp = ip + 20, *o = tcp + 20;
    int md5 = !!strstr(st, "md5sig"), ts = strstr(st, "tsopt") && s->has_ts, optlen = md5 * 20 + ts * 12, ttl = 64;
    char sni[256];
    const char *t;
    snprintf(sni, sizeof sni, "%s", fake_sni);
    if ((t = strstr(st, "sni="))) sscanf(t + 4, "%250[^,]", sni);
    if ((t = strstr(st, "autottl="))) {
        int hops = (s->ttl <= 64 ? 64 : s->ttl <= 128 ? 128 : 255) - s->ttl;
        ttl = hops - atoi(t + 8);
        ttl = ttl < 3 ? 3 : ttl > 20 ? 20 : ttl;
    } else if ((t = strstr(st, "ttl=")))
        ttl = atoi(t + 4);
    *ttl_out = ttl;

    int tlen = 20 + optlen + mk_hello(o + optlen, sni, !!strstr(st, "pad517")), iplen = 20 + tlen;
    memcpy(pk, s->eth, 14);
    memset(ip, 0, 40 + optlen);
    ip[0] = 0x45, ip[2] = iplen >> 8, ip[3] = iplen, ip[6] = 0x40, ip[8] = ttl, ip[9] = 6;
    arc4random_buf(ip + 4, 2);
    memcpy(ip + 12, &s->saddr, 4), memcpy(ip + 16, &s->daddr, 4);
    uint16_t c = csum(ip, 20, 0);
    ip[10] = c >> 8, ip[11] = c;

    tcp[0] = lport >> 8, tcp[1] = lport, tcp[2] = s->dport >> 8, tcp[3] = s->dport;
    wr32(tcp + 4, s->seq - (strstr(st, "badseq") ? 10000 : 0));
    wr32(tcp + 8, s->ack);
    tcp[12] = (5 + optlen / 4) << 4, tcp[13] = 0x18, tcp[14] = tcp[15] = 0xff;   // PSH|ACK
    if (ts) {   // наш timestamp = тот, что был в SYN, плюс прошедшие миллисекунды (у macOS такт 1 мс)
        o[0] = o[1] = 1, o[2] = 8, o[3] = 10;
        wr32(o + 4, s->ts_ecr + (uint32_t)(now_ms() - s->t0)), wr32(o + 8, s->ts_val), o += 12;
    }
    if (md5) o[0] = 19, o[1] = 18, arc4random_buf(o + 2, 16), o[18] = o[19] = 1;
    c = csum(tcp, tlen, (uint16_t)~csum(ip + 12, 8, 6 + tlen));   // псевдозаголовок: адреса + протокол + длина
    if (strstr(st, "badsum")) c ^= 0x5555;
    tcp[16] = c >> 8, tcp[17] = c;
    return 14 + iplen;
}

static void on_pkt(u_char *u, const struct pcap_pkthdr *h, const u_char *p) {
    (void)u;
    if (h->caplen < 14 + 20 + 20) return;
    const u_char *ip = p + 14, *tcp = ip + (ip[0] & 15) * 4, *end = p + h->caplen;
    if (tcp + 20 > end) return;
    if (tcp + (tcp[12] >> 4) * 4 < end) end = tcp + (tcp[12] >> 4) * 4;
    pthread_mutex_lock(&mu);
    struct slot *s = &slots[tcp[2] << 8 | tcp[3]];
    if (s->state == 1 && !memcmp(ip + 12, &s->daddr, 4) && (tcp[0] << 8 | tcp[1]) == s->dport) {
        memcpy(s->eth, p + 6, 6), memcpy(s->eth + 6, p, 6), s->eth[12] = 8, s->eth[13] = 0;
        memcpy(&s->saddr, ip + 16, 4);
        s->ack = rd32(tcp + 4) + 1, s->seq = rd32(tcp + 8), s->ttl = ip[8];
        for (const u_char *o = tcp + 20; o < end && *o;) {          // ищем опцию timestamp (8)
            if (*o == 1) { o++; continue; }
            if (o + 2 > end || o[1] < 2 || o + o[1] > end) break;
            if (*o == 8 && o[1] == 10) s->has_ts = 1, s->ts_val = rd32(o + 2), s->ts_ecr = rd32(o + 6);
            o += o[1];
        }
        s->state = 2;
        pthread_cond_broadcast(&cv);
    }
    pthread_mutex_unlock(&mu);
}

static void *sniff(void *a) {
    (void)a;
    pcap_loop(pc, -1, on_pkt, 0);
    fprintf(stderr, "pcap остановился: %s\n", pcap_geterr(pc));
    exit(1);
}

static int rdn(int fd, uint8_t *b, int n) {
    for (int r; n > 0; b += r, n -= r)
        if ((r = (int)read(fd, b, n)) <= 0) return -1;
    return 0;
}
static int wrn(int fd, const void *v, int n) {
    const uint8_t *b = v;
    for (int r; n > 0; b += r, n -= r)
        if ((r = (int)write(fd, b, n)) <= 0) return -1;
    return 0;
}

// ponytail: вместо hostlist — не трогаем российские зоны: там по SNI почти не блокируют, а фейки
// и разрезы могут не понравиться чужой анти-DDoS защите (перестраховка, на практике не проверено).
// Понадобится точнее — добавить файл-список.
static int is_ru(const uint8_t *h, int n) {
    static const char *tld[] = {".ru", ".su", ".xn--p1ai"};
    for (int i = 0; i < 3; i++) {
        int l = (int)strlen(tld[i]);
        if (n > l && !strncasecmp((const char *)h + n - l, tld[i], l)) return 1;
    }
    return 0;
}

// Первая порция данных от клиента: если это ClientHello — фейк, затем настоящий в два куска.
static int first_send(int r, uint16_t lport, const char *host, const char *st, const uint8_t *b, int n) {
    int sl, so = find_sni(b, n, &sl);
    if (so < 0 || is_ru(b + so, sl)) return wrn(r, b, n);

    struct timeval now;
    gettimeofday(&now, 0);
    struct timespec till = {now.tv_sec, (now.tv_usec + 300000) * 1000L};   // ждём SYN-ACK до 300 мс
    till.tv_sec += till.tv_nsec / 1000000000L, till.tv_nsec %= 1000000000L;
    pthread_mutex_lock(&mu);
    while (pc && slots[lport].state == 1 && !pthread_cond_timedwait(&cv, &mu, &till)) {}
    struct slot s = slots[lport];
    pthread_mutex_unlock(&mu);

    const char *t;
    int ttl = 0, sent = 0, rep = (t = strstr(st, "rep=")) ? atoi(t + 4) : repeats;
    if (s.state == 2 && !strstr(st, "nofake")) {
        uint8_t pk[1024];
        int len = mk_fake(pk, &s, lport, st, &ttl);
        for (int i = 0; i < rep; i++) sent += pcap_inject(pc, pk, len) == len;
    }
    if (verbose)
        fprintf(stderr, "%-28s [%s] фейков: %d ttl=%d (SYN-ACK ttl=%d)%s\n", host, st, sent, ttl, s.ttl,
                s.state == 2 ? "" : "  — SYN-ACK не пойман, идём без фейка");

    int cut = so + sl / 2;
    if ((t = strstr(st, "pos=")) && atoi(t + 4) > 0 && atoi(t + 4) < n) cut = atoi(t + 4);
    uint8_t tb[16384 + 5];
    if (strstr(st, "tlsrec") && cut > 5) {          // одна TLS-запись -> две, граница там же, где разрез TCP
        int rl = b[3] << 8 | b[4], c1 = cut - 5;
        memcpy(tb, b, cut), tb[3] = c1 >> 8, tb[4] = c1;
        memcpy(tb + cut, b, 3), tb[cut + 3] = (rl - c1) >> 8, tb[cut + 4] = rl - c1;
        memcpy(tb + cut + 5, b + cut, n - cut);
        b = tb, n += 5;
    }
    int one = 1, def = 64, dis = !!strstr(st, "disorder");
    if (dis) setsockopt(r, IPPROTO_IP, IP_TTL, &one, sizeof one);
    if (wrn(r, b, cut)) return -1;
    if (dis) setsockopt(r, IPPROTO_IP, IP_TTL, &def, sizeof def);
    return wrn(r, b + cut, n - cut);
}

// SOCKS5 UDP ASSOCIATE (нужен туннелю sing-box для голоса Discord и прочего UDP).
// Перед первым пакетом на новый адрес шлём с того же сокета пустышки: DPI судит о потоке
// по первым пакетам, сервер мусор просто игнорирует. Перехват тут не нужен вовсе.
// ponytail: только IPv4-адресаты; помним до 64 адресатов на ассоциацию, остальные идут без пустышек.
static void udp_assoc(int c) {
    static const uint8_t zeros[64];
    uint8_t b[65536 + 16], rep[10] = {5, 0, 0, 1, 127, 0, 0, 1};
    struct sockaddr_in any = {.sin_len = sizeof any, .sin_family = AF_INET}, a = any, cl = any, d, from;
    struct { uint32_t ip; uint16_t port; } seen[64];
    socklen_t l = sizeof a;
    int nseen = 0, n, i, u = socket(AF_INET, SOCK_DGRAM, 0), o = socket(AF_INET, SOCK_DGRAM, 0);
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (u < 0 || o < 0 || bind(u, (void *)&a, l) || getsockname(u, (void *)&a, &l) || bind(o, (void *)&any, sizeof any)) goto done;
    setsockopt(o, IPPROTO_IP, IP_BOUND_IF, &ifidx, sizeof ifidx);
    memcpy(rep + 8, &a.sin_port, 2);
    if (wrn(c, rep, 10)) goto done;

    struct pollfd pf[3] = {{c, POLLIN, 0}, {u, POLLIN, 0}, {o, POLLIN, 0}};
    while (poll(pf, 3, -1) >= 0 && !pf[0].revents) {      // управляющее TCP закрылось — конец ассоциации
        if (pf[1].revents) {                               // от клиента: [0 0 frag=0 atyp=1 ip port] данные
            l = sizeof from, n = (int)recvfrom(u, b, sizeof b, 0, (void *)&from, &l);
            if (n >= 10 && !b[2] && b[3] == 1) {
                cl = from, d = any;
                memcpy(&d.sin_addr, b + 4, 4), memcpy(&d.sin_port, b + 8, 2);
                for (i = 0; i < nseen && (seen[i].ip != d.sin_addr.s_addr || seen[i].port != d.sin_port); i++) {}
                if (i == nseen && nseen < 64) {
                    seen[nseen].ip = d.sin_addr.s_addr, seen[nseen++].port = d.sin_port;
                    int nf = ntohs(d.sin_port) >= 1024 ? ufakes : 0;   // DNS, NTP и т.п. не трогаем
                    for (i = 0; i < nf; i++) sendto(o, zeros, sizeof zeros, 0, (void *)&d, sizeof d);
                    if (verbose) fprintf(stderr, "udp %s:%d пустышек: %d\n", inet_ntoa(d.sin_addr), ntohs(d.sin_port), nf);
                }
                sendto(o, b + 10, n - 10, 0, (void *)&d, sizeof d);
            }
        }
        if (pf[2].revents) {                               // от сервера: заворачиваем обратно клиенту
            l = sizeof d, n = (int)recvfrom(o, b + 10, sizeof b - 10, 0, (void *)&d, &l);
            if (n >= 0 && cl.sin_port) {
                memset(b, 0, 3), b[3] = 1, memcpy(b + 4, &d.sin_addr, 4), memcpy(b + 8, &d.sin_port, 2);
                sendto(u, b, n + 10, 0, (void *)&cl, sizeof cl);
            }
        }
    }
done:
    if (u >= 0) close(u);
    if (o >= 0) close(o);
}

static void *conn(void *arg) {
    int c = (int)(intptr_t)arg, r = -1, n, one = 1;
    uint8_t b[16384];
    char host[256], port[8], st[256];
    uint16_t lport = 0;
    struct addrinfo hint = {.ai_family = AF_INET, .ai_socktype = SOCK_STREAM}, *ai = 0;
    snprintf(st, sizeof st, "%s", fool);

    // SOCKS5: без авторизации либо логин/пароль, где логин — стратегия для этого соединения
    if (rdn(c, b, 2) || b[0] != 5 || (n = b[1], rdn(c, b, n))) goto out;
    int auth = memchr(b, 2, n) != 0;
    if (wrn(c, auth ? "\5\2" : "\5\0", 2)) goto out;
    if (auth) {
        if (rdn(c, b, 2) || (n = b[1], rdn(c, b, n))) goto out;
        memcpy(st, b, n), st[n] = 0;
        if (rdn(c, b, 1) || (n = b[0], rdn(c, b, n)) || wrn(c, "\1\0", 2)) goto out;
    }
    if (rdn(c, b, 4)) goto out;
    int cmd = b[1];
    if (b[3] == 1) {
        if (rdn(c, b, 4)) goto out;
        inet_ntop(AF_INET, b, host, sizeof host);
    } else if (b[3] == 3) {
        if (rdn(c, b, 1) || (n = b[0], rdn(c, b, n))) goto out;
        memcpy(host, b, n), host[n] = 0;
    } else
        goto fail;
    if (rdn(c, b, 2)) goto out;
    if (cmd == 3) { udp_assoc(c); goto out; }
    if (cmd != 1) goto fail;
    snprintf(port, sizeof port, "%d", b[0] << 8 | b[1]);
    if (getaddrinfo(host, port, &hint, &ai)) goto fail;

    // Порт занимаем до connect, чтобы поток pcap знал, чей SYN-ACK ловить
    struct sockaddr_in la = {.sin_len = sizeof la, .sin_family = AF_INET}, *ra = (void *)ai->ai_addr;
    socklen_t ll = sizeof la;
    if ((r = socket(AF_INET, SOCK_STREAM, 0)) < 0 || bind(r, (void *)&la, ll) || getsockname(r, (void *)&la, &ll))
        goto fail;
    lport = ntohs(la.sin_port);
    setsockopt(r, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    setsockopt(r, IPPROTO_IP, IP_BOUND_IF, &ifidx, sizeof ifidx);   // мимо VPN-туннеля, строго через наш интерфейс
    pthread_mutex_lock(&mu);
    slots[lport] = (struct slot){.state = 1, .daddr = ra->sin_addr.s_addr, .dport = ntohs(ra->sin_port), .t0 = now_ms()};
    pthread_mutex_unlock(&mu);
    if (connect(r, ai->ai_addr, ai->ai_addrlen)) goto fail;
    if (wrn(c, "\5\0\0\1\0\0\0\0\0\0", 10)) goto out;

    // ponytail: EOF с любой стороны закрывает обе; half-close добавить, если что-то сломается
    struct pollfd pf[2] = {{c, POLLIN, 0}, {r, POLLIN, 0}};
    for (int first = 1;;) {
        if (poll(pf, 2, -1) < 0) goto out;
        for (int i = 0; i < 2; i++) {
            if (!pf[i].revents) continue;
            if ((n = (int)read(pf[i].fd, b, sizeof b)) <= 0) goto out;
            if (i == 0 && first ? first_send(r, lport, host, st, b, n) : wrn(pf[1 - i].fd, b, n)) goto out;
            if (i == 0) first = 0;
        }
    }
fail:
    wrn(c, "\5\5\0\1\0\0\0\0\0\0", 10);
out:
    if (lport) {
        pthread_mutex_lock(&mu);
        slots[lport].state = 0;
        pthread_mutex_unlock(&mu);
    }
    if (ai) freeaddrinfo(ai);
    if (r >= 0) close(r);
    close(c);
    return 0;
}

static void selftest(void) {
    uint8_t b[600], pk[1024];
    int len = 0, n = mk_hello(b, "example.com", 0), off = find_sni(b, n, &len), ttl;
    assert(off > 0 && len == 11 && !memcmp(b + off, "example.com", 11));
    assert((b[3] << 8 | b[4]) == n - 5 && (b[7] << 8 | b[8]) == n - 9);
    assert(find_sni(b, 60, &len) == -1 && find_sni((uint8_t *)"GET / HTTP/1.1\r\nHost: a\r\n\r\n012345678901234567", 44, &len) == -1);
    assert(mk_hello(b, "example.com", 1) == 517 && find_sni(b, 517, &len) == off);

    struct slot s = {.state = 2, .ttl = 52, .has_ts = 1, .ts_val = 7, .ts_ecr = 9, .t0 = now_ms(),
                     .saddr = htonl(0xc0a80105), .daddr = htonl(0x5db8d822), .seq = 1000, .ack = 2000, .dport = 443};
    const char *sts[] = {"none", "md5sig", "tsopt", "md5sig,tsopt,pad517,sni=ya.ru"};
    for (int i = 0; i < 4; i++) {                      // при любых опциях обе суммы должны сходиться в 0
        int flen = mk_fake(pk, &s, 50000, sts[i], &ttl), tlen = flen - 34, hdr = (pk[46] >> 4) * 4;
        assert(ttl == 64 && csum(pk + 14, 20, 0) == 0);
        assert(csum(pk + 34, tlen, (uint16_t)~csum(pk + 26, 8, 6 + tlen)) == 0);
        assert(hdr == 20 + (i & 1) * 20 + (i >> 1) * 12);
        assert(find_sni(pk + 34 + hdr, tlen - hdr, &len) > 0 && len == (i == 3 ? 5 : (int)strlen(fake_sni)));
    }
    assert(is_ru((uint8_t *)"www.Gosuslugi.RU", 16) && is_ru((uint8_t *)"a.xn--p1ai", 10) && !is_ru((uint8_t *)"rutracker.org", 13) && !is_ru((uint8_t *)".ru", 3));
    mk_fake(pk, &s, 50000, "autottl=2", &ttl);
    assert(ttl == 10);                                 // 64 - 52 = 12 хопов, минус 2
    puts("selftest ok");
}

int main(int argc, char **argv) {
    const char *iface = "en0";
    int port = 1080, o, one = 1;
    char err[PCAP_ERRBUF_SIZE];
    struct bpf_program fp;
    int nopcap = 0;
    while ((o = getopt(argc, argv, "i:p:s:f:r:u:nvT")) != -1) switch (o) {
        case 'u': ufakes = atoi(optarg); break;
        case 'n': nopcap = 1; break;      // без перехвата и без root: TCP-фейков не будет, UDP работает
        case 'i': iface = optarg; break;
        case 'p': port = atoi(optarg); break;
        case 's': fake_sni = optarg; break;
        case 'f': fool = optarg; break;
        case 'r': repeats = atoi(optarg); break;
        case 'v': verbose = 1; break;
        case 'T': selftest(); return 0;
        default: fprintf(stderr, "usage: sudo %s [-i en0] [-p 1080] [-s sni] [-f стратегия] [-r N] [-v]   (стратегии — в шапке desync.c)\n", argv[0]); return 2;
        }
    if (strlen(fake_sni) > 250 || strlen(fool) > 250) return fprintf(stderr, "слишком длинный аргумент\n"), 2;

    if (!(ifidx = if_nametoindex(iface))) return fprintf(stderr, "нет интерфейса %s\n", iface), 1;
    if (!nopcap) {
        if (!(pc = pcap_create(iface, err))) return fprintf(stderr, "pcap: %s\n", err), 1;
        pcap_set_snaplen(pc, 128), pcap_set_immediate_mode(pc, 1), pcap_set_timeout(pc, 100);
        if (pcap_activate(pc) < 0) return fprintf(stderr, "pcap %s: %s (нужен sudo)\n", iface, pcap_geterr(pc)), 1;
        if (pcap_datalink(pc) != DLT_EN10MB) return fprintf(stderr, "%s: не Ethernet/Wi-Fi\n", iface), 1;
        if (pcap_compile(pc, &fp, "tcp[tcpflags] & (tcp-syn|tcp-ack) = (tcp-syn|tcp-ack)", 1, PCAP_NETMASK_UNKNOWN) ||
            pcap_setfilter(pc, &fp) || pcap_setdirection(pc, PCAP_D_IN))
            return fprintf(stderr, "pcap: %s\n", pcap_geterr(pc)), 1;
    }

    struct sockaddr_in a = {.sin_len = sizeof a, .sin_family = AF_INET, .sin_port = htons(port), .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    int ls = socket(AF_INET, SOCK_STREAM, 0);
    setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    if (bind(ls, (void *)&a, sizeof a) || listen(ls, 128)) return perror("listen"), 1;

    // BPF уже открыт — root больше не нужен
    const char *uid = getenv("SUDO_UID"), *gid = getenv("SUDO_GID");
    if (getuid() == 0 && uid && gid && (setgid(atoi(gid)) || setuid(atoi(uid)))) return perror("setuid"), 1;

    signal(SIGPIPE, SIG_IGN);
    pthread_t t;
    pthread_attr_t at;
    pthread_attr_init(&at), pthread_attr_setdetachstate(&at, PTHREAD_CREATE_DETACHED);
    if (pc) pthread_create(&t, &at, sniff, 0);
    fprintf(stderr, "macdesync: socks5://127.0.0.1:%d, %s, стратегия=%s, fake sni=%s, udp-пустышек=%d%s\n", port, iface, fool,
            fake_sni, ufakes, pc ? "" : "  [без перехвата: TCP-фейки выключены]");
    for (int c;;)
        if ((c = accept(ls, 0, 0)) >= 0 && pthread_create(&t, &at, conn, (void *)(intptr_t)c)) close(c);
}
