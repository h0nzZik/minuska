#!/usr/bin/env bash

gendir="./generated"
echo "Compiling $gendir"
for vfile in "$gendir"/*.v; do
    coqc -R minuska/theories Minuska "$vfile"
done