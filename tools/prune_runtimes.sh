#!/bin/sh
# Delete non-linux-x64 native runtime folders from a .NET build output dir (they are never loaded here; rebuilds recreate them).
#   usage: tools/prune_runtimes.sh /home/exedev/lazerproof/oracle/bin/Release/net10.0
d="$1/runtimes"; [ -d "$d" ] || exit 0
for r in "$d"/*; do [ "$(basename "$r")" = linux-x64 ] || rm -rf -- "$r"; done
