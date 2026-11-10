#!/bin/bash
# Обход блокировок без VPN для ВСЕХ приложений, включая голос Discord.
# Папка самодостаточна: desync — прокси с фейками (исходник desync.c рядом),
# sing-box — туннель, tun.json — его конфиг. Ничего в систему не устанавливается.
# Спросит пароль администратора. Остановить — Ctrl-C или закрыть это окно.
cd "$(dirname "$0")" || exit 1

# Файлы, пришедшие по AirDrop или из архива, macOS помечает и не даёт запускать — снимаем пометку со своей папки
xattr -dr com.apple.quarantine . 2>/dev/null

IF=$(route -n get default 2>/dev/null | awk '/interface:/{print $2}')
[ -n "$IF" ] || { echo "Нет подключения к сети."; exit 1; }
if [[ "$IF" == utun* ]] || route -n get 1.1.1.1 2>/dev/null | grep -q 'interface: utun'; then
  echo "Сейчас включён VPN: трафик идёт через его туннель."
  echo "Выключите VPN и запустите этот файл снова."
  exit 1
fi
./desync -T >/dev/null 2>&1 || { echo "desync не запускается на этом Маке. Пересоберите его — команда в первых строках desync.c."; exit 1; }
./sing-box version >/dev/null 2>&1 || { echo "sing-box не запускается на этом Маке (см. ПРОЧТИ.txt)."; exit 1; }

exec > >(tee run.log) 2>&1
echo "Сеть: $IF. Когда появится строка 'sing-box started', можно пользоваться."
# Один root-шелл держит оба процесса: умер любой из них или закрыли окно — гасим второй,
# чтобы туннель не остался висеть без прокси (иначе пропадёт интернет).
sudo /bin/sh -c '
  pkill -f "^\./desync" 2>/dev/null
  ./desync -v -i "$1" & D=$!
  sleep 1
  ./sing-box run -c tun.json --disable-color & S=$!
  trap "kill $S $D 2>/dev/null; exit 0" INT TERM HUP
  while kill -0 $S 2>/dev/null && kill -0 $D 2>/dev/null; do sleep 1; done
  kill $S $D 2>/dev/null
' sh "$IF"
echo "Остановлено."
