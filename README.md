# DynASM
DynASM is a dynamic assembler, useful for code generation, for example as part of JIT compilation.  
This project is almost entirely based on code released as part of [LuaJIT](https://github.com/LuaJIT/LuaJIT) by Mike Pall.

I have no intention of changing the API of DynASM, so any documentation for the original LuaJIT project should also apply to this one.

## Current Aims
* Addition of NEON support for ARM and ARM64 targets
* Investigation into whether current ARM target is sufficient to run on restricted environments (e.g. ARMv7-M)

## Links
* [DynASM page on LuaJIT website](https://luajit.org/dynasm.html)
* [Unofficial DynASM documentation](http://corsix.github.io/dynasm-doc/) by Peter Cawley