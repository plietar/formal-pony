# Copyright (c) 2012-2015, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import os, glob, string
import subprocess

modules = ["ch2o/prelude", "src"]

Rs = '-R ch2o ch2o -R src pony'
env = DefaultEnvironment(ENV = os.environ,tools=['default', 'Coq'], COQFLAGS=Rs)

# Coq dependencies
vs = [x for m in modules for x in glob.glob(m + '/*.v')]
if os.system('coqdep ' + Rs + ' ' + ' '.join(map(str, vs)) + ' > deps'): Exit(2)
ParseDepends('deps')

# Coq files
for v in vs:
  env.Coq(v)

env.Depends('main/Extracted.pre.hs', 'src/Extract.vo')

env.Command('main/Extracted.hs',
            'main/Extracted.pre.hs',
            "(cat main/Extracted.in.hs && tail -n+15 < $SOURCE) > $TARGET")

env.Depends('main/Extracted.hs', 'main/Extracted.in.hs')

env.CoqIdeScript('coqidescript', [])
