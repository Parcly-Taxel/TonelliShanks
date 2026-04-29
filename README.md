This little project contains a [Velvet](https://github.com/verse-lab/velvet) formalisation of the [Tonelli–Shanks algorithm](https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm) for finding [square roots modulo an odd prime](https://en.wikipedia.org/wiki/Quadratic_residue). It was done for Ilya Sergey's Formal Specification and Design Techniques (CS5232) course at the National University of Singapore, AY25/26 Semester 2.

## How to run and verify the implementation

After cloning the repository you will see only one file in the `TonelliShanks` folder, `Algorithm.lean`. The Tonelli–Shanks algorithm is defined in that file as the Velvet method `tonelliShanks`, accepting in order
* a natural number `p`
* a proof `hp` that `p` is an odd prime
* the number `n` whose square root modulo `p` is sought. Its type is `ZMod p`, but natural numbers or integers can be provided for this argument and Lean will automatically coerce.

Here [ZMod p](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Defs.html#ZMod) is the type of integers modulo `p`, the algorithm's natural setting.

It returns an option type, either
* `some r` where `r : ZMod p` satisfies `r ^ 2 = n`, or
* `none` if no such `r` exists (i.e. `n` is not a quadratic residue modulo `p`).

The algorithm may be run by issuing the following command at any point in `Algorithm.lean` after the definition of `tonelliShanks`:
```lean
#eval (tonelliShanks p hp n).run
```

The result is shown in the Lean Infoview. For example, to find the square roots of 2 and 5 modulo 97, type
```lean
#eval (tonelliShanks 97 (by decide) 2).run -- DivM.res (some 83); 83^2 % 97 = 2
#eval (tonelliShanks 97 (by decide) 5).run -- DivM.res none; 5 has no square root modulo 97
```

(`decide` is a convenient inline way to prove that _small_ numbers are odd primes. For larger numbers it recurses too deeply and an external proof needs to be provided.)
