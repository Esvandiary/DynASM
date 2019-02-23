# DynASM
DynASM is a dynamic assembler, useful for code generation, for example as part of JIT compilation.  
This project is primarily based on code released as part of [LuaJIT](https://github.com/LuaJIT/LuaJIT) by Mike Pall.

I have no intention of changing the API of DynASM, so any documentation for the original LuaJIT project should also apply to this one.

## Additions and changes from LuaJIT's DynASM
| Change                            | Status                     |
| :-------------------------------- | :------------------------- |
| **New Target:** ARMv7-M (Thumb-2) | Complete, but experimental |

PRs adding or fixing functionality with any targets are very welcome, as are issue reports related to my changes.  
I am also happy to look at issues related to any x86 and ARM targets, but may not necessarily be in a position to solve them.

## Current Aims
* Documentation for ARMv7-M target
* Addition of NEON support for ARM and ARM64 targets

## Links
* [DynASM page on LuaJIT website](https://luajit.org/dynasm.html)
* [Unofficial DynASM documentation](http://corsix.github.io/dynasm-doc/) for x86 by Peter Cawley