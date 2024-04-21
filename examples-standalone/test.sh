#!/usr/bin/env bash

set -e

# https://stackoverflow.com/a/246128/6209703
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pushd "$SCRIPT_DIR"

TEMPDIR="$(pwd)/_temp"
TIME=$(which time)

rm -rf "$TEMPDIR"
mkdir -p "$TEMPDIR"


run10times() {
  for run in {1..10}; do "$@"; done
}

runCase() {
  local name="$1"
  local interpreter="$2"
  local input="$3"
  local depth="$4"
  local expout="$5"

  output=$(mktemp)
  echo "Running test '$name'"
  "$TIME" --output "$output.time" --format "%e" "$interpreter" --depth "$depth" --output-file "$output" "$input" 2>/dev/null >/dev/null
  diff "$output" "$expout"
  cat "$output.time"
  rm -f "$output"
}

doCompile() {
  local cmd="$@"
  echo "Compiling: minuska compile $cmd" 
  minuska compile $cmd 2>/dev/null >/dev/null && echo "Compilation finished."
}


rm -rf ./interpreters
mkdir -p ./interpreters

if doCompile ./m/fail-invalid-semantics.m interpreters/invalid.exe ; then
  echo "ERROR: an invalid language definition compiles!"
  exit 1
fi


doCompile ./m/decrement.m ./interpreters/decrement
echo "Decrement tests"
runCase "dec into 2" ./interpreters/decrement ./m/decrement.d/three 2 ./m/decrement.d/two
runCase "dec into 1" ./interpreters/decrement ./m/decrement.d/three 3 ./m/decrement.d/one


doCompile ./m/decrement-builtin.m ./interpreters/decrement-builtin
runCase "dec builtin into -1" ./interpreters/decrement-builtin ./m/decrement-builtin.d/cfg_3 5 ./m/decrement-builtin.d/cfg_minus_1

doCompile ./m/arith.m ./interpreters/arith
runCase "arith-01" ./interpreters/arith ./m/arith.d/01 20 ./m/arith.d/01.result

doCompile ./m/imp.m ./interpreters/imp
runCase "imp-01" ./interpreters/imp ./m/imp.d/01 20 ./m/imp.d/01.result
runCase "imp-lookup" ./interpreters/imp ./m/imp.d/00-assign-lookup-trivial.imp 20 ./m/imp.d/00-assign-lookup-trivial.result
runCase "imp-count-10" ./interpreters/imp ./m/imp.d/03-count-10.imp 1000 ./m/imp.d/03-count-10.result


doCompile ./m/two-counters.m ./interpreters/two-counters
runCase "two-counters.10" ./interpreters/two-counters ./m/two-counters.d/10         50000000 ./m/two-counters.d/10.result
runCase "two-counters.100" ./interpreters/two-counters ./m/two-counters.d/100       50000000 ./m/two-counters.d/100.result
runCase "two-counters.1'000" ./interpreters/two-counters ./m/two-counters.d/1000     50000000 ./m/two-counters.d/1000.result
runCase "two-counters.10'000" ./interpreters/two-counters ./m/two-counters.d/10000   50000000 ./m/two-counters.d/10000.result
runCase "two-counters.100'000" ./interpreters/two-counters ./m/two-counters.d/100000  50000000 ./m/two-counters.d/100000.result
runCase "two-counters.1'000'000" ./interpreters/two-counters ./m/two-counters.d/1000000 50000000 ./m/two-counters.d/1000000.result
