#!/usr/bin/env bash

prefix=$(cat <<EOF
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
    flattened
    naive_interpreter
    default_static_model
    notations
.

Require Extraction.
Extraction Language OCaml.

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))"
.


EOF
)

suffix=$(cat <<EOF

Definition interp :=
        naive_interpreter rules
    .


Fixpoint interp_loop
        (fuel : nat)
        (g : GroundTerm)
        : option GroundTerm
    :=
    match fuel with
    | 0 => Some g
    | S fuel' =>
        match (interp g) with
        | None => Some g
        | Some g' => interp_loop fuel' g' 
        end
    end.

Definition result (fuel : nat) := interp_loop fuel term_to_reduce.

EOF
)

outdir="./generated"
echo "Generating $outdir"
rm -rf "$outdir"
mkdir -p "$outdir"
for src in ./rec-2015-convecs/REC/*.rec; do
    name=$(basename --suffix ".rec" "$src" )
    tgt="$outdir/$name.v"
    echo "$src -> $tgt"
    #if grep -q 'if' "$src"; then
    #    echo "(Skipping due to use of the conditional)"
    #    continue
    #fi
    > "$tgt"
    echo "$prefix" >> "$tgt"
    ./rec.sh "$src" >> "$tgt" 2>/dev/null
    res="$?"
    echo "TopRes: $res"
    if [ "$res" -eq 3 ]; then
        echo "Error in translation"
        rm -f "$tgt"
        continue
    fi
    echo "$suffix" >> "$tgt"
    echo "Extraction \"$name\" result." >> "$tgt"
done
