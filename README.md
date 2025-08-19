# coverage-check

This repository contains an Agda formalization of one of the coverage checking algorithms for pattern matching presented in the paper "Warnings for pattern matching" by Luc Maranget.

> Luc Maranget. 2007. Warnings for pattern matching. J. Funct. Programming 17, 3 (May 2007), 387–421. <https://doi.org/10.1017/S0956796807006223>

Specifically, we formalize the usefulness checking algorithm $\mathcal{U}_\text{rec}$ presented in Section 3.1 and the exhaustiveness checking algorithm built on top of it.
We prove that a pattern matrix is indeed exhaustive if the algorithm returns `true`, and that there exists a sequence of values that are not covered if the algorithm returns `false`.
This formalization is compatible with agda2hs, allowing us to extract readable Haskell code from it!

Tested with Agda v2.7.0, agda-stdlib v2.0, and agda2hs 39e9b0c.
