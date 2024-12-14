module Extra where

open import Function using (_∘_; _⇔_; mk⇔)

--------------------------------------------------------------------------------
-- Extra lemmas

module _ where
  open import Data.List as List using (List; []; _∷_)
  open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
  open import Data.List.Relation.Unary.First as First using (First; [_]; _∷_)
  open import Relation.Unary using (Pred; ∁; _⊆_)

  ¬First⇒¬Any : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
    → ∁ Q ⊆ P
    → ∁ (First P Q) ⊆ ∁ (Any Q)
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (here qx) = ¬pqxxs [ qx ]
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (there qxs) =
    ¬First⇒¬Any ¬q⇒p (¬pqxxs ∘ (¬q⇒p (¬pqxxs ∘ [_]) ∷_)) qxs

module _ {n} where
  open import Data.Fin using (Fin)
  open import Data.Fin.Subset using (Subset; _∉_; _∪_; Empty)
  open import Data.Fin.Subset.Properties using (x∈p∪q⁺; x∈p∪q⁻)
  open import Data.Product using (_×_; _,_; uncurry)
  open import Data.Sum using (inj₁; inj₂)
  open import Relation.Nullary.Negation using (¬_; contraposition)

  module _ {x : Fin n} {p q} where

    x∉p∪q⁻ˡ : x ∉ p ∪ q → x ∉ p
    x∉p∪q⁻ˡ = contraposition (x∈p∪q⁺ ∘ inj₁)

    x∉p∪q⁻ʳ : x ∉ p ∪ q → x ∉ q
    x∉p∪q⁻ʳ = contraposition (x∈p∪q⁺ ∘ inj₂)

    x∉p∪q⁻ : x ∉ p ∪ q → x ∉ p × x ∉ q
    x∉p∪q⁻ x∉p∪q = x∉p∪q⁻ˡ x∉p∪q , x∉p∪q⁻ʳ x∉p∪q


  module _ {p q : Subset n} where

    Empty∪⁺ : Empty p → Empty q → Empty (p ∪ q)
    Empty∪⁺ emptyP emptyQ (x , x∈p∪q) with x∈p∪q⁻ _ _ x∈p∪q
    ... | inj₁ x∈p = emptyP (x , x∈p)
    ... | inj₂ x∈q = emptyQ (x , x∈q)

    Empty∪⁻ : Empty (p ∪ q) → Empty p × Empty q
    Empty∪⁻ emptyP∪Q =
      (λ (x , x∈p) → emptyP∪Q (x , x∈p∪q⁺ (inj₁ x∈p))) ,
      (λ (x , x∈q) → emptyP∪Q (x , x∈p∪q⁺ (inj₂ x∈q)))

    Empty∪⇔ : (Empty p × Empty q) ⇔ Empty (p ∪ q)
    Empty∪⇔ = mk⇔ (uncurry Empty∪⁺) Empty∪⁻
