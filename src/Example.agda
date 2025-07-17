module Example where

open import Data.Fin.Base using (zero; suc)
open import Data.Nat.Base using (zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; erefl)
open import Relation.Nullary.Decidable using (yes; no)

open import Pattern
open import Exhaustiveness

private
  variable
    α β : Ty

--------------------------------------------------------------------------------
-- Example from the paper (but made polymorphic)

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
