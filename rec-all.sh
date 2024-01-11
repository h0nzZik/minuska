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
        : (GroundTerm*nat)
    :=
    match fuel with
    | 0 => (g, 0)
    | S fuel' =>
        match (interp g) with
        | None => (g, fuel')
        | Some g' => interp_loop fuel' g' 
        end
    end.

Definition result (fuel : nat) := interp_loop fuel term_to_reduce.

EOF
)

generateSingle() {
    src="$1"
    tgt="$2"

    echo "$src -> $tgt"
    > "$tgt"
    echo "$prefix" >> "$tgt"
    ./rec.sh "$src" >> "$tgt" 2>/dev/null
    res="$?"
    echo "TopRes: $res"
    if [ "$res" -eq 3 ]; then
        echo "Error in translation"
        rm -f "$tgt"
        return 3
    fi
    echo "$suffix" >> "$tgt"
    echo "Extraction \"$name\" result." >> "$tgt"
}

outdir="./generated"
echo "Generating $outdir"
rm -rf "$outdir"
mkdir -p "$outdir"
for src in ./rec-2015-convecs/REC/*.rec ./rec-2015-convecs/REC-SIMPLE/*.rec; do
    name=$(basename --suffix ".rec" "$src" )
    tgt="$outdir/$name.v"
    generateSingle "$src" "$tgt"
done
