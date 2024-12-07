module Example where

open import Data.Fin using (zero; suc)
open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (yes; no)

open import Pattern
open import Usefulness

--------------------------------------------------------------------------------

nat : Ty
nat .numCons = 2
nat .args zero = []
nat .args (suc zero) = nat ∷ []
nat .inhabCon = zero
nat .inhabArgs = []

pattern zero′ = con zero []
pattern suc′ n = con (suc zero) (n ∷ [])

patmat₁ : PatMat (nat ∷ nat ∷ [])
patmat₁ =
  (zero′ ∷ zero′ ∷ []) ∷
  (suc′ ∙ ∷ zero′ ∷ []) ∷
  (zero′ ∷ suc′ ∙ ∷ []) ∷
  []

patmat₂ : PatMat (nat ∷ nat ∷ [])
patmat₂ =
  (zero′ ∷ zero′ ∷ []) ∷
  (suc′ ∙ ∷ zero′ ∷ []) ∷
  (zero′ ∷ suc′ ∙ ∷ []) ∷
  (suc′ ∙ ∷ suc′ ∙ ∷ []) ∷
  []

vals₁ : Vals (nat ∷ nat ∷ [])
vals₁ = suc′ zero′ ∷ suc′ zero′ ∷ []

vals₂ : Vals (nat ∷ nat ∷ [])
vals₂ = suc′ zero′ ∷ zero′ ∷ []

_ : match? vals₁ patmat₁ ≡ no _
_ = refl

_ : match? vals₂ patmat₁ ≡ yes _
_ = refl

_ : exhaustive? patmat₁ ≡ inj₂ (suc′ zero′ ∷ suc′ zero′ ∷ [] , _)
_ = refl

_ : exhaustive? patmat₂ ≡ inj₁ _
_ = refl
