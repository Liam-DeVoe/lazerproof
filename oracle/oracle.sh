#!/bin/sh
# Wrapper: runs the Release build of the oracle with the user-local dotnet, under the machine-wide
# heavy-job semaphore (tools/heavy). `batch` runs go through the transparent result cache
# (tools/oracle_cache.py) unless ORACLE_NOCACHE=1 or a side-effecting/non-deterministic flag is used.
export DOTNET_ROOT="${DOTNET_ROOT:-$HOME/.dotnet}" DOTNET_CLI_TELEMETRY_OPTOUT=1
export DOTNET_GCHeapHardLimit="${DOTNET_GCHeapHardLimit:-0x30000000}"
here="$(dirname "$0")"; root="$here/.."
if [ "$1" = "batch" ] && [ -z "$ORACLE_NOCACHE" ]; then
  case " $* " in
    *" --dump-playable"*|*" --dump-env"*|*" --steps-out"*|*" --timing"*) ;;
    *) exec "$root/tools/heavy" python3 -I "$root/tools/oracle_cache.py" "$@" ;;
  esac
fi
exec "$root/tools/heavy" "$here/bin/Release/net10.0/oracle" "$@"
