#!/usr/bin/env bash


cat - | grep -A3 'bench:' | head -n -1 | ./parse-log-groups.py
