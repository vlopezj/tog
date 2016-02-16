#!/usr/bin/env bash

DIR="$1"

while read a; do
    cmd="$a"
    fname=$DIR/$(echo $a | tr "\\ /\t" "[_*]").task

    if [ ! -e $fname ]; then
        echo $a > "$fname"
    fi

    plain_fname=${fname%.*}.plain
    make $plain_fname
done

    

