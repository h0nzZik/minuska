#!/usr/bin/env bash

INPUT_FILE="$1"

inputWithoutComments() {
    cat "$INPUT_FILE" \
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
        | sed -e '1,/RULES/d'
}


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

echo 'Definition rules := ['

rules \
    | sed 's/^[ \t]*//;s/[ \t]*$//'  \
    | sed -e 's/->/=>/g' \
    | sed -e 's/\(.*\)/\1;/' \
    | head --bytes=-2

echo '].'

#cat "$INPUT_FILE" \
#    | cut -f1 -d"%" \
#    | sed -e 's/\([A-Z]\)/$\1/g'

