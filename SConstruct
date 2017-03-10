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


def add_qualified(target, source, env):
  subprocess.check_call(['sed', '-e', 's/module .* where/module Extracted where/',
                         '-e', '/^module/a\\\nimport qualified Data.Bits',
                         '-e', '/^module/a\\\nimport qualified Data.Char'],
                        stdin=open(str(source[0])),
                        stdout=open(str(target[0]), 'w'))

# Coq files
for v in vs:
  env.Coq(v)

env.Depends('main/Extracted.pre.hs', 'src/Extract.vo')

env.Command('main/Extracted.hs',
            'main/Extracted.pre.hs',
            Action(add_qualified))

env.CoqIdeScript('coqidescript', [])
