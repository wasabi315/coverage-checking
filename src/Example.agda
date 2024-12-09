module Example where

open import Data.Fin using (zero; suc)
open import Data.Fin.Subset using (∁)
open import Data.Fin.Subset.Properties using (nonempty?)
open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (yes; no)

open import Pattern
open import Exhaustiveness

private
  variable
    α β : Ty

--------------------------------------------------------------------------------
-- Example from the paper (but made polymorphic)

-- type 'a mylist = Nil | One of 'a | Cons of 'a * 'a mylist
mylist : Ty → Ty
mylist α .numCons = 3
mylist α .args zero = []
mylist α .args (suc zero) = α ∷ []
mylist α .args (suc (suc zero)) = α ∷ mylist α ∷ []
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

Q : PatMat (mylist α ∷ mylist β ∷ [])
Q =
  (nil      ∷ ∙        ∷ []) ∷
  (∙        ∷ nil      ∷ []) ∷
  (one ∙    ∷ ∙        ∷ []) ∷
  (∙        ∷ one ∙    ∷ []) ∷
  (cons ∙ ∙ ∷ ∙        ∷ []) ∷
  (∙        ∷ cons ∙ ∙ ∷ []) ∷
  []

-- P is non-exhaustive, witnessed by one (inhab α) ∷ one (inhab β) ∷ []
_ : exhaustive? (P {α} {β}) ≡ inj₂ (one (inhab α) ∷ one (inhab β) ∷ [] , _)
_ = refl

-- Q is exhaustive, so we got a function of type `(vs : Vals (mylist α ∷ mylist β ∷ [])) → Match vs Q` inside the inj₁
_ : exhaustive? (Q {α} {β}) ≡ inj₁ _
_ = refl
