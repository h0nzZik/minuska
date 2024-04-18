#!/usr/bin/env bash

set -e

TEMPDIR="$(pwd)/_temp"

rm -rf "$TEMPDIR"
mkdir -p "$TEMPDIR"

runCase() {
  local interpreter="$1"
  local input="$2"
  local depth="$3"
  local expout="$4"

  output=$(mktemp)
  "$interpreter" --depth "$depth" --output-file "$output" "$input"
  diff "$output" "$expout"
  rm -f "$output"
}


rm -rf ./interpreters
mkdir -p ./interpreters
minuska compile ./m/decrement.m ./interpreters/decrement
runCase ./interpreters/decrement ./m/decrement.d/three 1 ./m/decrement.d/two
runCase ./interpreters/decrement ./m/decrement.d/three 2 ./m/decrement.d/one
