#!/bin/bash
# One-time Forgejo setup (code browser for ~/lazerproof). Run as: sudo bash tools/forgejo/setup.sh
# - Forgejo 16.0.6 (sha256-verified binary), runs as system user `git`, SQLite, HTTP on port 3000.
# - Reachable at https://osu-judgments.exe.xyz:3000/ ; exe.dev only proxies non-default ports to users
#   with VM access (docs/proxy.md), so this is private. Registration disabled, no SSH, no mailer.
# - Creates admin user `osu` with a random password stored in /home/exedev/.forgejo_admin (mode 600).
set -euo pipefail
BIN_SRC=${BIN_SRC:-/tmp/claude-1000/-home-exedev/5a067c7e-69f6-4190-93e6-f7fa504e1337/scratchpad/fj/forgejo}
echo "b90e22c2e5534fd7705d93d81ecea792b00f15cad0ee7bbc3061c65bf9524293  $BIN_SRC" | sha256sum -c -
install -m 755 "$BIN_SRC" /usr/local/bin/forgejo
id git >/dev/null 2>&1 || adduser --system --shell /bin/bash --gecos 'Forgejo' --group --disabled-password --home /home/git git
mkdir -p /var/lib/forgejo /etc/forgejo
chown git:git /var/lib/forgejo; chmod 750 /var/lib/forgejo
if [ ! -f /etc/forgejo/app.ini ]; then
SECRET=$(/usr/local/bin/forgejo generate secret SECRET_KEY); ITOKEN=$(/usr/local/bin/forgejo generate secret INTERNAL_TOKEN)
cat > /etc/forgejo/app.ini <<EOF
APP_NAME = lazerproof
RUN_USER = git
RUN_MODE = prod
WORK_PATH = /var/lib/forgejo

[server]
PROTOCOL = http
HTTP_ADDR = 0.0.0.0
HTTP_PORT = 3000
DOMAIN = osu-judgments.exe.xyz
ROOT_URL = https://osu-judgments.exe.xyz:3000/
DISABLE_SSH = true
OFFLINE_MODE = true
LFS_START_SERVER = false

[database]
DB_TYPE = sqlite3
PATH = /var/lib/forgejo/data/forgejo.db

[security]
INSTALL_LOCK = true
SECRET_KEY = $SECRET
INTERNAL_TOKEN = $ITOKEN

[service]
DISABLE_REGISTRATION = true
REQUIRE_SIGNIN_VIEW = false
DEFAULT_KEEP_EMAIL_PRIVATE = true

[repository]
ROOT = /var/lib/forgejo/data/forgejo-repositories
DEFAULT_BRANCH = master

[log]
MODE = file
LEVEL = Warn
ROOT_PATH = /var/lib/forgejo/log

[mailer]
ENABLED = false

[indexer]
REPO_INDEXER_ENABLED = true
EOF
fi
# Pre-generate secrets Forgejo would otherwise try to write back into the (read-only) app.ini.
if ! grep -q '^JWT_SECRET' /etc/forgejo/app.ini; then
  printf '\n[oauth2]\nJWT_SECRET = %s\n' "$(/usr/local/bin/forgejo generate secret JWT_SECRET)" >> /etc/forgejo/app.ini
fi
if ! grep -q '^LFS_JWT_SECRET' /etc/forgejo/app.ini; then
  sed -i "/^LFS_START_SERVER/a LFS_JWT_SECRET = $(/usr/local/bin/forgejo generate secret LFS_JWT_SECRET)" /etc/forgejo/app.ini
fi
chown root:git /etc/forgejo/app.ini; chmod 640 /etc/forgejo/app.ini
cat > /etc/systemd/system/forgejo.service <<'EOF'
[Unit]
Description=Forgejo (lazerproof code browser)
After=network.target

[Service]
User=git
Group=git
WorkingDirectory=/var/lib/forgejo
ExecStart=/usr/local/bin/forgejo web --config /etc/forgejo/app.ini
Restart=always
Environment=USER=git HOME=/home/git FORGEJO_WORK_DIR=/var/lib/forgejo
Nice=10
MemoryMax=600M

[Install]
WantedBy=multi-user.target
EOF
systemctl daemon-reload
systemctl enable forgejo
systemctl restart forgejo
for i in $(seq 1 30); do curl -sf -o /dev/null http://localhost:3000/ && break; sleep 1; done
if [ ! -f /home/exedev/.forgejo_admin ]; then
  PW=$(head -c 18 /dev/urandom | base64 | tr -d '/+=')
  sudo -u git /usr/local/bin/forgejo --config /etc/forgejo/app.ini admin user create \
    --username osu --password "$PW" --email osu@localhost --admin --must-change-password=false
  install -m 600 -o exedev -g exedev /dev/null /home/exedev/.forgejo_admin
  printf 'user=osu\npassword=%s\nurl=https://osu-judgments.exe.xyz:3000/\n' "$PW" > /home/exedev/.forgejo_admin
fi
systemctl is-active forgejo && echo "Forgejo up: https://osu-judgments.exe.xyz:3000/  (login in /home/exedev/.forgejo_admin)"
