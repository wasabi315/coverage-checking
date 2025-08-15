# coverage-check

This repository contains an Agda formalisation of one the coverage checking algorithms for pattern matching presented in the paper "Warnings for pattern matching" by Luc Maranget.

> Luc Maranget. 2007. Warnings for pattern matching. J. Funct. Programming 17, 3 (May 2007), 387–421. <https://doi.org/10.1017/S0956796807006223>

Specifically, we formalise the usefulness checking algorithm $\mathcal{U}_\text{rec}$ presented in Section 3.1 and the exhaustiveness checking algorithm built on top of it.
We proved that a pattern matrix is indeed exhaustive if the algorithm returns `true`, and there exists a sequence of values that are not covered if the algorithm returns `false`.

```agda
-- type list = Nil | One unit | Cons unit list

P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ◂ —   ◂ ⌈⌉) ∷
  (—   ◂ nil ◂ ⌈⌉) ∷
  []

-- P is non-exhaustive, witnessed by one unit ∷ one unit ∷ []
_ : decNonExhaustive P ≡ Right ((one unit ◂ one unit ◂ ⌈⌉) ⟨ _ ⟩)
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ nil      ◂ ⌈⌉) ∷
  (one —    ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ one —    ◂ ⌈⌉) ∷
  (cons — — ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ cons — — ◂ ⌈⌉) ∷
  []

-- Q is exhaustive, so we get a total matching function of type `∀ vs → Match Q vs`
_ : decNonExhaustive Q ≡ Left (Erased (the (∀ vs → Match Q vs) _))
_ = refl
```

This formalisation is compatible with agda2hs, so we can extract a readable Haskell code from it!

Tested with Agda v2.7.0, agda-stdlib v2.0, and agda2hs 39e9b0c.
