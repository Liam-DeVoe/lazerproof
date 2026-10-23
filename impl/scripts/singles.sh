#!/bin/bash
# every osu! mod alone (randomised settings) on the first N corpus maps: Rust vs Lean
# usage: impl/scripts/singles.sh WORKDIR N SEED
W=$1; N=${2:-100}; SEED=${3:-41}
for A in EZ NF HR TC BL ST AL SG AT CN RX AP SO TR SI FR BU SY TD SV2 HT DC DT NC SD PF HD FL AC TP DA CL RD MR WG GR DF WU WD BR AD MU NS MG RP AS DP BM; do
  python3 -I ~/lazerproof/impl/scripts/bm_rs_vs_lean.py --work $W/$A --limit $N --mods single:$SEED:$A > $W/$A.log 2>&1
  echo "$A $(tail -1 $W/$A.log | head -c 200)"
  rm -rf $W/$A
done
