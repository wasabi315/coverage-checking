module Extra where

open import Data.Fin as Fin using (Fin)
open import Data.Fin.Subset as Subset using (Subset; _∉_; _∪_; Empty)
open import Data.Fin.Subset.Properties as Subset using (x∈p∪q⁺; x∈p∪q⁻)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.First as First using (First; [_]; _∷_)
open import Data.Product as Product using (_×_; _,_; uncurry)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable as Dec using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Unary using (Pred; ∁; _⊆_)

--------------------------------------------------------------------------------
-- Extra lemmas

≟-refl : ∀ {n} (i : Fin n) → (i Fin.≟ i) ≡ yes refl
≟-refl i with i Fin.≟ i
... | yes refl = refl
... | no ¬refl = contradiction refl ¬refl

¬First⇒All : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
  → ∁ Q ⊆ P
  → ∁ (First P Q) ⊆ All P
¬First⇒All ¬q⇒p {[]} _ = []
¬First⇒All ¬q⇒p {x ∷ xs} ¬pqxxs =
  let px = ¬q⇒p (¬pqxxs ∘ [_]) in
  px ∷ ¬First⇒All ¬q⇒p (¬pqxxs ∘ (px ∷_))

module _ {n} {x : Fin n} {p q} where

  x∉p∪q⁻ˡ : x ∉ p ∪ q → x ∉ p
  x∉p∪q⁻ˡ = contraposition (x∈p∪q⁺ ∘ inj₁)

  x∉p∪q⁻ʳ : x ∉ p ∪ q → x ∉ q
  x∉p∪q⁻ʳ = contraposition (x∈p∪q⁺ ∘ inj₂)

  x∉p∪q⁻ : x ∉ p ∪ q → x ∉ p × x ∉ q
  x∉p∪q⁻ x∉p∪q = x∉p∪q⁻ˡ x∉p∪q , x∉p∪q⁻ʳ x∉p∪q


module _ {n} {p q : Subset n} where

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
