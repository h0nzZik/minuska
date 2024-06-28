#!/usr/bin/env bash

set -e

# https://stackoverflow.com/a/246128/6209703
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pushd "$SCRIPT_DIR"

TIME=$(which time)


testInCoq() {
  rm -rf coqfiles
  mkdir -p coqfiles
  
  echo "Generating *.v files"
  minuska def2coq ./languages/imp/imp.m coqfiles/imp.v
  minuska gt2coq ./imp-ast/count-1.imp coqfiles/count1.v
  minuska gt2coq ./imp-ast/count-2.imp coqfiles/count2.v
  minuska gt2coq ./imp-ast/count-3.imp coqfiles/count3.v
  minuska gt2coq ./imp-ast/count-4.imp coqfiles/count4.v
  minuska gt2coq ./imp-ast/count-5.imp coqfiles/count5.v
  minuska gt2coq ./imp-ast/count-6.imp coqfiles/count6.v
  minuska gt2coq ./imp-ast/count-7.imp coqfiles/count7.v

  pushd coqfiles > /dev/null
  for vfile in *.v; do
    echo "Compiling $vfile"
    coqc -R . Test "$vfile" > /dev/null
  done 
  popd > /dev/null
  cp test-imp/testCount*.v ./coqfiles/
  pushd coqfiles > /dev/null
  for testvfile in testCount*.v; do
    echo "coqc $testvfile"
    "$TIME" --output "$testvfile.time" --format "%e" coqc -R . Test "$testvfile" 2> /dev/null
    cat "$testvfile.time"
  done
  popd > /dev/null
}

testInCoq