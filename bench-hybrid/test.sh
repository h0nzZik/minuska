#!/usr/bin/env bash

set -e

# https://stackoverflow.com/a/246128/6209703
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

pushd "$SCRIPT_DIR" > /dev/null

TIME=$(which time)

LOGFILEOUT="./log-stdout.txt"
LOGFILEERR="./log-stderr.txt"
if [[ -n "$VERBOSE" ]]; then
  LOGFILEOUT=/dev/stdout
  LOGFILEERR=/dev/stderr
fi

testInCoq() {
  rm -rf coqfiles
  mkdir -p coqfiles
  
  echo "Generating *.v files"
  minuska def2coq ./languages/imp/imp.m coqfiles/imp.v
  minuska gt2coq --builtins klike ./imp-ast/count-1.imp coqfiles/count1.v
  minuska gt2coq --builtins klike ./imp-ast/count-2.imp coqfiles/count2.v
  minuska gt2coq --builtins klike ./imp-ast/count-3.imp coqfiles/count3.v
  minuska gt2coq --builtins klike ./imp-ast/count-4.imp coqfiles/count4.v
  minuska gt2coq --builtins klike ./imp-ast/count-5.imp coqfiles/count5.v
  minuska gt2coq --builtins klike ./imp-ast/count-6.imp coqfiles/count6.v
  minuska gt2coq --builtins klike ./imp-ast/count-7.imp coqfiles/count7.v
  minuska def2coq ./languages/two-counters/two-counters.m coqfiles/twocounters.v
  minuska gt2coq --builtins klike ./tc-ast/tc10.ast coqfiles/tc10.v
  minuska gt2coq --builtins klike ./tc-ast/tc20.ast coqfiles/tc20.v
  minuska gt2coq --builtins klike ./tc-ast/tc50.ast coqfiles/tc50.v
  minuska gt2coq --builtins klike ./tc-ast/tc100.ast coqfiles/tc100.v



  echo "Compiling *.v files"
  pushd coqfiles > /dev/null
  for vfile in *.v; do
    echo "Compiling $vfile" > "$LOGFILEOUT"
    minuska info run -- coqc -R . Test "$vfile" > "$LOGFILEOUT" 2>"$LOGFILEERR"
  done 
  popd > /dev/null
  cp test-imp/testCount*.v ./coqfiles/
  cp test-tc/testTC*.v ./coqfiles/
  pushd coqfiles > /dev/null
  for testvfile in test*.v; do
    echo "coqc $testvfile"
    "$TIME" --output "$testvfile.time" --format "%e" minuska info run -- coqc -R . Test "$testvfile" 2> "$LOGFILEERR" | grep 'Finished transaction'
    cat "$testvfile.time"
  done
  popd > /dev/null
}

testInCoq
