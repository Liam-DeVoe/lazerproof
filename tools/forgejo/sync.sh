#!/bin/bash
# Mirror ~/lazerproof (all branches + tags) to the LOCAL Forgejo (http://localhost:3000/osu/lazerproof, private).
# Called by .git/hooks/post-commit (in background) and by cron every 5 min. Never pushes anywhere else.
cd /home/exedev/lazerproof || exit 1
exec 9>/tmp/osu-forgejo-sync.lock; flock -n 9 || exit 0
git push -q --all forgejo 2>>/home/exedev/lazerproof/status/forgejo-sync.log
git push -q --tags forgejo 2>>/home/exedev/lazerproof/status/forgejo-sync.log
