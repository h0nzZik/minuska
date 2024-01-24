#!/usr/bin/env python3

import sys

vhead = open('theories/benchmark-template-head.v', 'r').read()

lines = list(open('theories/benchmark-list.v.template', 'r').readlines())

for i,l in enumerate(lines):
  fname = 'theories/generated{}.v'.format(i)
  #print(f"fname: {fname}, l: {l}")
  with open(fname, 'w') as fw:
    fw.write(vhead + "\n\n" + 'Time Compute ' + l + '.\n')


