## Compilation

To generate/update the `RocqMakefile` from `_RocqProject`:

`rocq makefile -f _RocqProject -o RocqMakefile`

Then, to compile/check all proof scripts listed in `_RocqProject_`:

`make -f RocqMakefile all`

To remove generated files, run:

`make -f RocqMakefile cleanall`

Compatibility tested with Rocq `9.10.0`.

## Contents

- SVL for gradual verification : [SVL.v](SVL.v)
- GVL for gradual verification : [GVL.v](GVL.v)
