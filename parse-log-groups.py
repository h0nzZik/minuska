#!/usr/bin/env python3

import sys
import itertools
import re
#import platform

#if not (platform.python_version_tuple() >= (3,12,0)):
#    print("Python version too low: {}".format(platform.python_version_tuple()))

lines = list(sys.stdin)

groups = list(itertools.batched(lines, 3))

#print(f'groups: {groups}')
p1 = re.compile('[^"]*"([^"]*)"[^"]*')
p2 = re.compile('bench: (.*)')
p3 = re.compile('Finished transaction in ([0-9]+.[0-9]+) secs.*')

for i,g in enumerate(groups):
    #print(f'group {i}: {g}')

    #print(f"{i}: {l1}")
    m1 = p1.match(g[0])
    #print(m1)
    if not m1:
        #print("Not found, skipping")
        continue
    content = m1.group(1)
    #print(content)
    m2 = p2.match(content)
    #print(m2)
    name = m2.group(1)
    #print(f'name: {name}')
    time = p3.match(g[2]).group(1)
    #print(f'time: {time}')
    print(f'{name}, {time}')
        
