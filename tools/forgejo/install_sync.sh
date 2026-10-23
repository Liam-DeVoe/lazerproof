#!/bin/bash
# One-time: mirror the repo to the local private Forgejo and keep it in sync. Run as exedev (no sudo):
#   bash ~/lazerproof/tools/forgejo/install_sync.sh
# - remote `forgejo` = http://localhost:3000/osu/lazerproof.git (local only); token from ~/.forgejo_token,
#   kept in ~/.forgejo-git-credentials (mode 600), not in the remote URL.
# - post-commit hook pushes in the background after every commit (any agent); cron every 5 min as backup.
set -euo pipefail
R=/home/exedev/lazerproof; cd "$R"
umask 077
printf 'http://osu:%s@localhost:3000\n' "$(cat /home/exedev/.forgejo_token)" > /home/exedev/.forgejo-git-credentials
git remote get-url forgejo >/dev/null 2>&1 || git remote add forgejo http://localhost:3000/osu/lazerproof.git
git config credential.http://localhost:3000.helper "store --file /home/exedev/.forgejo-git-credentials"
umask 022
cat > .git/hooks/post-commit <<'EOF'
#!/bin/sh
# mirror to the local Forgejo (tools/forgejo/sync.sh); background so commits stay fast
setsid /home/exedev/lazerproof/tools/forgejo/sync.sh >/dev/null 2>&1 < /dev/null &
EOF
chmod +x .git/hooks/post-commit tools/forgejo/sync.sh
( crontab -l 2>/dev/null | grep -v 'tools/forgejo/sync.sh'; echo '*/5 * * * * /home/exedev/lazerproof/tools/forgejo/sync.sh' ) | crontab -
tools/forgejo/sync.sh
git ls-remote forgejo | head -3
echo "synced: https://osu-judgments.exe.xyz:3000/osu/lazerproof (login: ~/.forgejo_admin)"
