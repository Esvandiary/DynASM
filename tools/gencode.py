#!/usr/bin/env python
import sys
import collections

if len(sys.argv) < 3:
    print("usage: {0} <input-file> <output-file>".format(sys.argv[0]))
    exit(0)

with open(sys.argv[1], 'r') as f:
    lines = [l.strip() for l in f if len(l) > 2 and l[0] != '#']

xl = []
for l in [k.split(',', 2) for k in lines]:
    commentsplit = l[2].split(' ', 1)
    xl.append((
        l[0],
        '{0:08x}'.format(int(''.join([c for c in l[1] if c != ' ']), 2)),
        commentsplit[0],
        commentsplit[1] if len(commentsplit) > 1 else ''))

d = collections.OrderedDict()
for l in xl:
    if l[0] in d:
        d[l[0]][0] += "|{0}{1}".format(l[1], l[2])
        d[l[0]][1] += l[3]
    else:
        d[l[0]] = [l[1] + l[2], l[3]]

with open(sys.argv[2], 'w') as f:
    f.writelines('  {0} = "{1}",{2}\n'.format('["{0}"]'.format(k) if '.' in k else k, v[0], v[1]) for k, v in d.items())
