module Extra where

--------------------------------------------------------------------------------
-- Extra lemmas

module _ where
  open import Data.Bool.Base using (true; false)
  open import Data.Empty using (⊥-elim)
  open import Data.Fin.Base using (Fin; zero; suc)
  import Data.Fin.Properties as Fin
  open import Data.List.Base as List using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
  open import Data.List.Relation.Unary.First as First using (First; [_]; _∷_)
  open import Data.Nat.Base using (ℕ; zero; suc)
  open import Data.Product.Base as Product using (∃-syntax; _,_)
  open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
  open import Function.Base using (id; _∘_)
  open import Relation.Unary using (Pred; ∁; _⊆_; Decidable)
  open import Relation.Nullary.Negation.Core using (¬_; contradiction)
  open import Relation.Nullary.Decidable.Core using (Dec; yes; no; _because_; _⊎-dec_; toSum)
  open import Relation.Nullary.Reflects using (invert)

  ¬First⇒¬Any : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
    → ∁ Q ⊆ P
    → ∁ (First P Q) ⊆ ∁ (Any Q)
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (here qx) = ¬pqxxs [ qx ]
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (there qxs) =
    ¬First⇒¬Any ¬q⇒p (¬pqxxs ∘ (¬q⇒p (¬pqxxs ∘ [_]) ∷_)) qxs

  allOrCounterexample : ∀ {p n} {P : Fin n → Set p}
    → Decidable P
    → (∀ x → P x) ⊎ (∃[ x ] ¬ P x)
  allOrCounterexample {n = zero} P? = inj₁ (⊥-elim ∘ Fin.¬Fin0)
  allOrCounterexample {n = suc n} P? with P? zero
  ... | false because [¬P0] = inj₂ (zero , invert [¬P0])
  ... | true because [P0] =
        Sum.map (Fin.∀-cons (invert [P0])) (Product.map suc id) (allOrCounterexample (P? ∘ suc))
