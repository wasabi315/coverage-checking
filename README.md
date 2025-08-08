# coverage-check

This repository contains an Agda formalisation of one the coverage checking algorithms for pattern matching presented in the paper "Warnings for pattern matching" by Luc Maranget.

> Luc Maranget. 2007. Warnings for pattern matching. J. Funct. Programming 17, 3 (May 2007), 387–421. <https://doi.org/10.1017/S0956796807006223>

Specifically, we formalise the usefulness checking algorithm $\mathcal{U}_\text{rec}$ presented in Section 3.1 and the exhaustiveness checking algorithm built on top of it.
We prove that a matrix of pattern is indeed exhaustive if the algorithm returns `true`, and there exists a sequence of values that are not covered if the algorithm returns `false`.

```agda
-- data Mylist a = Nil | One a | Cons a (Mylist a)
mylist : Ty → Ty
mylist α .numCons = 3
mylist α .argsTy zero = []
mylist α .argsTy (suc zero) = α ∷ []
mylist α .argsTy (suc (suc zero)) = α ∷ mylist α ∷ []
mylist α .inhabCon = zero
mylist α .inhabArgs = []

pattern nil = con zero []
pattern one x = con (suc zero) (x ∷ [])
pattern cons x xs = con (suc (suc zero)) (x ∷ xs ∷ [])

P : PatMat (mylist α ∷ mylist β ∷ [])
P =
  (nil ∷ ∙   ∷ []) ∷
  (∙   ∷ nil ∷ []) ∷
  []

-- P is non-exhaustive, witnessed by one (inhab α) ∷ one (inhab β) ∷ []
_ : exhaustive? (P {α} {β}) ≡ inj₂ (one (inhab α) ∷ one (inhab β) ∷ [] , _)
_ = refl

Q : PatMat (mylist α ∷ mylist β ∷ [])
Q =
  (nil      ∷ ∙        ∷ []) ∷
  (∙        ∷ nil      ∷ []) ∷
  (one ∙    ∷ ∙        ∷ []) ∷
  (∙        ∷ one ∙    ∷ []) ∷
  (cons ∙ ∙ ∷ ∙        ∷ []) ∷
  (∙        ∷ cons ∙ ∙ ∷ []) ∷
  []

-- Q is exhaustive, so we get a "total" matching function of type `∀ vs → Match Q vs` inside the inj₁
_ : exhaustive? (Q {α} {β}) ≡ inj₁ _
_ = refl
```

Tested with Agda v2.7.0 and agda-stdlib v2.0.
