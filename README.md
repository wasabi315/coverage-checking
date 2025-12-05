# coverage-check

This repository contains a verified implementation of a coverage checking algorithm for pattern matching, as presented in the paper "Warnings for pattern matching" by Luc Maranget.

> Luc Maranget. 2007. Warnings for pattern matching. J. Funct. Programming 17, 3 (May 2007), 387–421. <https://doi.org/10.1017/S0956796807006223>

Specifically, we mechanized in Agda the usefulness checking algorithm $\mathcal{U}_\text{rec}$ presented in Section 3.1 and the exhaustiveness/non-redundancy checking algorithm built on top of it. Correctness and termination are proved in the mechanization.

This mechanization is compatible with agda2hs, which allows us to extract readable Haskell code and use it as a library.

## Example

```agda
-- type list = Nil | One unit | Cons unit list

P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ∷ —   ∷ []) ∷
  (—   ∷ nil ∷ []) ∷ []

-- P is non-exhaustive, as witnessed by the following list of patterns
-- Values covered by these witness patterns are proved not to match any row in P
_ : decExhaustive P
  ≡ Left (
      ((cons — —  ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((cons — —  ∷ one —    ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ one —    ∷ []) ⟨ _ ⟩) ∷ [])
_ = refl

-- All rows in P are non-redundant
_ : decAllNonRedundant P ≡ Right _
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ∷ —        ∷ []) ∷
  (—        ∷ nil      ∷ []) ∷
  (one —    ∷ —        ∷ []) ∷
  (—        ∷ one —    ∷ []) ∷
  (cons — — ∷ —        ∷ []) ∷
  (—        ∷ cons — — ∷ []) ∷ []

-- Q is exhaustive, so we obtain a total matching function of type
--   `∀ vs → FirstMatch Q vs`
_ : decExhaustive Q ≡ Right (Erased (the (∀ vs → FirstMatch Q vs) _))
_ = refl

-- The last row of Q is redundant, so we obtain a proof of uselessness for the last row
_ : decAllNonRedundant Q
  ≡ (Left
      $ there
      $ there
      $ there
      $ there
      $ there
      $ Erased
          (the
            (¬ Useful
              ( (nil      ∷ —        ∷ []) ∷
                (—        ∷ nil      ∷ []) ∷
                (one —    ∷ —        ∷ []) ∷
                (—        ∷ one —    ∷ []) ∷
                (cons — — ∷ —        ∷ []) ∷ [])
                (—        ∷ cons — — ∷ []))
            _)
      ∷ [])
_ = refl
```

See [highlighted Agda code](https://wasabi315.github.io/coverage-checking) for details.

## Building

Run `make` to typecheck and generate Haskell code. The generated Haskell code will be placed in the `lib` directory.

Tested with Agda v2.8.0, agda-stdlib v2.3, and agda2hs v1.4.
