#!/usr/bin/env bash

set -e

TEMPDIR="$(pwd)/_temp"

rm -rf "$TEMPDIR"
mkdir -p "$TEMPDIR"

runCase() {
  local name="$1"
  local interpreter="$2"
  local input="$3"
  local depth="$4"
  local expout="$5"

  output=$(mktemp)
  echo "Running test '$name'"
  "$interpreter" --depth "$depth" --output-file "$output" "$input"
  diff "$output" "$expout"
  rm -f "$output"
}


rm -rf ./interpreters
mkdir -p ./interpreters

minuska compile ./m/decrement.m ./interpreters/decrement
runCase "dec into 2" ./interpreters/decrement ./m/decrement.d/three 2 ./m/decrement.d/two
runCase "dec into 1" ./interpreters/decrement ./m/decrement.d/three 3 ./m/decrement.d/one


minuska compile ./m/decrement-builtin.m ./interpreters/decrement-builtin
runCase "dec builtin into -1" ./interpreters/decrement-builtin ./m/decrement-builtin.d/cfg_3 5 ./m/decrement-builtin.d/cfg_minus_1

minuska compile ./m/arith.m ./interpreters/arith
runCase "arith-01" ./interpreters/arith ./m/arith.d/01 20 ./m/arith.d/01.result

