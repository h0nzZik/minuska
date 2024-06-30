#!/usr/bin/env bash

set -e

# https://stackoverflow.com/a/246128/6209703
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pushd "$SCRIPT_DIR" > /dev/null

TIME=$(which time)

# https://stackoverflow.com/a/10983009/6209703
mydir=$(mktemp -d "${TMPDIR:-/tmp/}$(basename $0).XXXXXXXXXXXX")

./generate-v-files.py

for f in theories/generated*.v; do
  b="$(basename --suffix ".v" "$f")"
  #echo "B: $b"
  "${TIME}" --format="%e" --output "$mydir/outertime.txt" -- coqc $f 2>/dev/null | tail -n 3  | ./parse-log-groups.py | tr -d '\n' > "$mydir/out.txt"
  echo -n ", " >> "$mydir/out.txt"
  cat "$mydir/outertime.txt" | tr -d '\n' >> "$mydir/out.txt"
  cat "$mydir/out.txt"
  echo
done

#cat build_log.txt | ./parse-timing-log.sh | tee timing-log.txt
