#!/bin/sh
# Fail-path variant of oracle.sh (D80c): separate build (oracle_fail/bin), never touches oracle/bin or the oracle cache.
export DOTNET_ROOT="${DOTNET_ROOT:-$HOME/.dotnet}" DOTNET_CLI_TELEMETRY_OPTOUT=1
export DOTNET_GCHeapHardLimit="${DOTNET_GCHeapHardLimit:-0x30000000}"
here="$(dirname "$0")"; root="$here/.."
exec "$root/tools/heavy" "$here/bin/Release/net10.0/oracle_fail" "$@"
