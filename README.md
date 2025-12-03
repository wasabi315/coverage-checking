# coverage-check

This repository contains an Agda formalization of a coverage checking algorithm for pattern matching, as presented in the paper "Warnings for pattern matching" by Luc Maranget.

> Luc Maranget. 2007. Warnings for pattern matching. J. Funct. Programming 17, 3 (May 2007), 387–421. <https://doi.org/10.1017/S0956796807006223>

Specifically, we formalize the usefulness checking algorithm $\mathcal{U}_\text{rec}$ presented in Section 3.1 and the exhaustiveness checking algorithm built on top of it.
We prove that a pattern matrix is exhaustive if the algorithm returns `true`, and that there exists a sequence of values that are not covered if the algorithm returns `false`.
This is done by implementing an evidence-producing version of the algorithm, which computes witnessing patterns for usefulness.

```agda
-- type list = Nil | One unit | Cons unit list

P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ∷ —   ∷ []) ∷
  (—   ∷ nil ∷ []) ∷ []

-- P is non-exhaustive, as witnessed by the following list of patterns
_ : decExhaustive P
  ≡ Left (
      ((cons — —  ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((cons — —  ∷ one —    ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ one —    ∷ []) ⟨ _ ⟩) ∷ [])
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ∷ —        ∷ []) ∷
  (—        ∷ nil      ∷ []) ∷
  (one —    ∷ —        ∷ []) ∷
  (—        ∷ one —    ∷ []) ∷
  (cons — — ∷ —        ∷ []) ∷
  (—        ∷ cons — — ∷ []) ∷ []

-- Q is exhaustive, so we obtain a total matching function of type `∀ vs → FirstMatch Q vs`
_ : decExhaustive Q ≡ Right (Erased (the (∀ vs → FirstMatch Q vs) _))
_ = refl
```

This formalization is compatible with agda2hs, allowing us to extract readable Haskell code from it!

Tested with Agda v2.8.0, agda-stdlib v2.3, and agda2hs v1.4.
