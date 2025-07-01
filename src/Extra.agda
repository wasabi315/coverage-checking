module Extra where

open import Function using (_∘_; _⇔_; mk⇔)

--------------------------------------------------------------------------------
-- Extra lemmas

module _ where
  open import Data.Bool using (true; false)
  open import Data.List as List using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
  open import Data.List.Relation.Unary.First as First using (First; [_]; _∷_)
  open import Function.Base using (_∘_)
  open import Relation.Unary using (Pred; ∁; _⊆_; Decidable)
  open import Relation.Nullary.Negation.Core using (¬_; contradiction)
  open import Relation.Nullary.Decidable.Core using (_because_)
  open import Relation.Nullary.Reflects using (invert)

  ¬All¬⇒Any : ∀ {a p} {A : Set a} {P : Pred A p}
    → Decidable P
    → ∀ xs → ¬ All (¬_ ∘ P) xs → Any P xs
  ¬All¬⇒Any dec [] ¬∀¬ = contradiction [] ¬∀¬
  ¬All¬⇒Any dec (x ∷ xs) ¬∀¬ with dec x
  ... | true because [p] = here (invert [p])
  ... | false because [¬p] = there (¬All¬⇒Any dec xs (¬∀¬ ∘ _∷_ (invert [¬p])))

  ¬First⇒¬Any : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
    → ∁ Q ⊆ P
    → ∁ (First P Q) ⊆ ∁ (Any Q)
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (here qx) = ¬pqxxs [ qx ]
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (there qxs) =
    ¬First⇒¬Any ¬q⇒p (¬pqxxs ∘ (¬q⇒p (¬pqxxs ∘ [_]) ∷_)) qxs

