#!/usr/bin/env zsh
FILE="$1"

a=$(mktemp)
cat "$FILE" >! $a

. ./test-lib
cd ..
. $a
code=$?

rm -f $a
exit $?
