# Copyright (c) 2012-2013, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.

import os, glob, string

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])
vs = glob.glob('./*.v')
Rs = '-R . ""'

if os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + Rs + ' > deps'):
	Exit(2)

ParseDepends('deps')

for v in vs:
  env.Coq(v, COQFLAGS=Rs)

env.CoqIdeScript('coqidescript', [], COQFLAGS=Rs)

