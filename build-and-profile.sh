#!/usr/bin/env bash
make -C minuska-bench/ | tee build_log.txt
cat build_log.txt | ./parse-timing-log.sh | tee timing-log.txt
