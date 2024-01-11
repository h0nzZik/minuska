#!/usr/bin/env bash

gendir="./generated"
echo "Compiling (coqc) $gendir"
pushd "$gendir"
for vfile in *.v; do
    coqc -R ../minuska/theories Minuska "$vfile"
done
popd
