#!/usr/bin/env bash

gendir="./generated"
echo "Compiling (ocamlc) $gendir"
pushd "$gendir"
for name in $(cat ../rec-benchmark-selection.txt); do
    echo "Compiling $name"
    src="M$name.ml"
    srci="M$name.mli"
    cp "$name.ml" "M$name.ml"
    cp "$name.mli" "M$name.mli"
    tgt="$name.bin"
    drv="driverM$name.ml"
    echo > "$drv"
    echo "open M$name" >> "$drv"
    cat ../minuska/src/generic_driver.ml >> "$drv"
    ocamlc -w -20 -w -26 -o "$tgt"  "$srci" "$src" "$drv" 
done
popd
