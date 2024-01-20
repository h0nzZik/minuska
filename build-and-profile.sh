#!/usr/bin/env bash
make -C minuska/ | tee build_log.txt
cat build_log.txt | ./parse-timing-log.sh
