#!/usr/bin/env bash

DIR=`dirname "$0"`

INPUT_FILE=$(realpath "$1")

# TODO handle this in a better way (mktemp?)
TMP_FILE="$INPUT_FILE.tmp"

"$DIR/rec-2015-convecs/com/rec_normalize" -nothing "$INPUT_FILE" > "$TMP_FILE" 2>/dev/null

#cat "$TMP_FILE"

inputWithoutComments() {
    cat "$TMP_FILE" \
        | cut -f1 -d"%"
}

sorts() {
    inputWithoutComments \
        | sed -e '1,/SORTS/d' \
        | sed -n '/CONS/q;p'
}

cons() {
    inputWithoutComments \
        | sed -e '1,/CONS/d' \
        | sed -n '/OPNS/q;p'
}

opns() {
    inputWithoutComments \
        | sed -e '1,/OPNS/d' \
        | sed -n '/VARS/q;p'
}

vars() {
    inputWithoutComments \
        | sed -e '1,/VARS/d' \
        | sed -n '/RULES/q;p'
}

rules() {
    inputWithoutComments \
        | sed -e '1,/RULES/d' \
        | sed -n '/EVAL/q;p'
}

evalSection() {
    inputWithoutComments \
        | sed -e '1,/EVAL/d' \
        | sed -n '/END-SPEC/q;p' \
        | sed '/^\s*$/d' \
        | head -n 1
}

#evalSection | grep 'if'
rules | grep -q 'if' -- > /dev/null 2>/dev/null
res="$?"
if [ "$res" -eq "0" ]; then
    echo "(Skipping due to use of the conditional after preprocessing)"
    exit 3
fi


cons \
    | cut --delimiter=':' --fields='1' \
    | sed 's/^[ \t]*//;s/[ \t]*$//' \
    | sed -e 's/\(.*\)/Definition \1 := \"\1\"\./'


opns \
    | cut --delimiter=':' --fields='1' \
    | sed 's/^[ \t]*//;s/[ \t]*$//' \
    | sed -e 's/\(.*\)/Definition \1 := \"\1\"\./'

vars \
    | cut --delimiter=':' --fields='1' \
    | sed 's/^[ \t]*//;s/[ \t]*$//' \
    | sed -e 's/ /\n/g' \
    | sed -e 's/\(.*\)/Definition \1 := \"\1\"\./'

# We mark all identifiers with dollars
# and then we remove the dollar and add parentheses after the identifiers
# that start with a lowercase letter
processSymbolicTerm() {
    cat - \
    | sed 's/^[ \t]*//;s/[ \t]*$//'  \
    | sed -e 's/ //g' \
    | sed -e 's/\([[:alpha:]][[:alnum:]_]*\)/$\1/g' \
    | sed -e 's/\(\$[[:lower:]][[:alnum:]_]*\)$/\1()/g' \
    | sed -e 's/\(\$[[:lower:]][[:alnum:]_]*\)\(,\|)\)/\1()\2/g' \
    | sed -e 's/\$\([[:lower:]][[:alnum:]_]*\)\((\|,\|)\)/\1\2/g' \
    | sed -e 's/(/[</g' \
    | sed -e 's/)/>]/g' \
    
}

processRule() {
    cat - \
    | sed -e 's/\(.*\)->\(.*\)/rule "top"[<\1>] => "top"[<\2>] requires []/g' \
    | sed -e 's/\(.*\)/\1;/' \
    | head --bytes=-2
}

echo 'Definition rules := ['
rules | processSymbolicTerm | processRule

echo '].'

echo 'Definition terms_to_reduce := ['
evalSection \
    | processSymbolicTerm \
    | sed -e 's/\(.*\)/(aoo_app _ _ (\1)%concrete) ;/' \
    | head --bytes=-2
echo '].'

echo 'Definition term_to_reduce := hd (aoo_app _ _ ("top"[<>])%concrete) terms_to_reduce.'

exit 0