#!/usr/bin/env bash

set -e

# https://stackoverflow.com/a/246128/6209703
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pushd "$SCRIPT_DIR" > /dev/null

TEMPDIR="$(pwd)/_temp"
LOGFILEOUT="$TEMPDIR/log-stdout.txt"
LOGFILEERR="$TEMPDIR/log-stderr.txt"
if [[ -n "$VERBOSE" ]]; then
  LOGFILEOUT=/dev/stdout
  LOGFILEERR=/dev/stderr
fi
TIME=$(which time)

rm -rf "$TEMPDIR"
mkdir -p "$TEMPDIR"

> "$LOGFILEOUT"
> "$LOGFILEERR"

printlogs() {
  cat "$LOGFILEERR"
  cat "$LOGFILEOUT"
}
# Enable this when debugging
#trap printlogs 0

run10times() {
  for run in {1..10}; do "$@"; done
}

runCase() {
  local name="$1"
  local interpreter="$2"
  local input="$3"
  local depth="$4"
  local expout="$5"

  local output=$(mktemp)
  #echo "Running test '$name'"
  "$TIME" --output "$output.time" --format "%e" "$interpreter" --bench --depth "$depth" --output-file "$output" "$input" >>"$LOGFILEOUT" 2>>"$output".err
  if [[ -e "$expout" ]]; then
    diff "$output" "$expout"
  fi
  local extime=$(cat "$output".err | grep 'Execution' | cut -d ':' -f 2 | xargs)
  local parsetime=$(cat "$output".err | grep 'Parsing' | cut -d ':' -f 2 | xargs)
  local mytime=$(cat "$output.time")
  echo "$name,  $mytime,  $parsetime,  $extime"
  rm -f "$output"
}

doCompile() {
  local lang="$1"
  echo "Compiling $lang" 
  pushd ../languages/$lang/ > /dev/null
  dune build
  local state=$?
  dune install --prefix ./install-dir
  popd
  mkdir -p interpreters
  ln -s ../languages/$lang/install-dir/bin/run ./interpreters/$lang
  return $state
}


testNative() {
  rm -rf ./interpreters
  mkdir -p ./interpreters

  echo "== Compilation"
  if doCompile fail-invalid-semantics ; then
    echo "ERROR: an invalid language definition compiles!"
    exit 1
  fi

  doCompile decrement
  doCompile decrement-builtin
  doCompile arith
  doCompile imp
  doCompile two-counters


  echo
  echo "== Native (via OCaml extraction) benchmarks"
  echo "name, total, parsing, execution"

  #echo "Decrement tests"
  runCase "dec-into-2" ./interpreters/decrement-interpreter ./languages/decrement/tests/three.dec 2 DONOTTTEST
  runCase "dec-into-1" ./interpreters/decrement-interpreter ./languages/decrement/tests/three.dec 3 DONOTTTEST


  runCase "dec-builtin-into--1" ./interpreters/decrement-builtin-interpreter ./languages/decrement-builtin/tests/cfg_3.decb 5 ./languages/decrement-builtin/tests/cfg_minus_1

  runCase "arith-01" ./interpreters/arith-interpreter ./languages/arith/tests/01.arith 20 ./languages/arith/tests/01.result

  runCase "imp-01" ./interpreters/imp-interpreter ./languages/imp/tests/01.imp 20 ./languages/imp/tests/01.result
  #runCase "imp-lookup" ./interpreters/imp-interpreter ./languages/imp/tests/00-assign-lookup-trivial.imp 20 ./languages/imp/tests/00-assign-lookup-trivial.result

  runCase "imp-count-1" ./interpreters/imp-interpreter ./languages/imp/tests/count-1.imp 1000000 DONTTEST
  runCase "imp-count-2" ./interpreters/imp-interpreter ./languages/imp/tests/count-2.imp 1000000 DONTTEST
  runCase "imp-count-3" ./interpreters/imp-interpreter ./languages/imp/tests/count-3.imp 1000000 DONTTEST
  runCase "imp-count-4" ./interpreters/imp-interpreter ./languages/imp/tests/count-4.imp 1000000 DONTTEST
  runCase "imp-count-5" ./interpreters/imp-interpreter ./languages/imp/tests/count-5.imp 1000000 DONTTEST
  runCase "imp-count-6" ./interpreters/imp-interpreter ./languages/imp/tests/count-6.imp 1000000 DONTTEST
  runCase "imp-count-7" ./interpreters/imp-interpreter ./languages/imp/tests/count-7.imp 1000000 DONTTEST
  runCase "imp-count-10" ./interpreters/imp-interpreter ./languages/imp/tests/03-count-10.imp 1000000 ./languages/imp/tests/03-count-10.result

  runCase "two-counters.10"        ./interpreters/two-counters-interpreter ./languages/two-counters/tests/10.tc      50000000 ./languages/two-counters/tests/10.result
  runCase "two-counters.100"       ./interpreters/two-counters-interpreter ./languages/two-counters/tests/100.tc     50000000 ./languages/two-counters/tests/100.result
  runCase "two-counters.1'000"     ./interpreters/two-counters-interpreter ./languages/two-counters/tests/1000.tc    50000000 ./languages/two-counters/tests/1000.result
  runCase "two-counters.10'000"    ./interpreters/two-counters-interpreter ./languages/two-counters/tests/10000.tc   50000000 ./languages/two-counters/tests/10000.result
  runCase "two-counters.100'000"   ./interpreters/two-counters-interpreter ./languages/two-counters/tests/100000.tc  50000000 ./languages/two-counters/tests/100000.result
  runCase "two-counters.1'000'000" ./interpreters/two-counters-interpreter ./languages/two-counters/tests/1000000.tc 50000000 ./languages/two-counters/tests/1000000.result
}

testNative
