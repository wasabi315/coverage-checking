module CoverageCheck.Prelude where

open import Data.Empty public
  using (⊥; ⊥-elim)

open import Data.Fin.Base public
  using (Fin; zero; suc)
open import Data.Fin.Properties public
  using (¬Fin0)
  renaming (_≟_ to _≟Fin_; any? to anyFin?)

open import Data.List.Base public
  using (List; []; _∷_; _++_; concatMap; length)
  renaming (sum to sumList; map to mapList)
open import Data.List.Properties public
  using (sum-++; map-++; ++-identityʳ)

open import Data.List.Relation.Unary.All public
  using (All; []; _∷_)
  renaming (head to headAll; tail to tailAll; tabulate to tabulateAll)
open import Data.List.Relation.Unary.All.Properties public
  using (¬All⇒Any¬; All¬⇒¬Any; ¬Any⇒All¬)
  renaming (++⁺ to ++All⁺)

open import Data.List.Relation.Unary.Any public
  using (Any; here; there; any?)
  renaming (map to mapAny)
open import Data.List.Relation.Unary.Any.Properties public
  using (¬Any[])
  renaming (gmap to gmapAny; concat⁺ to concatAny⁺; concat⁻ to concatAny⁻;
            ++⁻ to ++Any⁻; ++⁺ˡ to ++Any⁺ˡ; ++⁺ʳ to ++Any⁺ʳ; map⁻ to mapAny⁻)

open import Data.List.Relation.Unary.First public
  using (First; _∷_)
  renaming (toAny to First⇒Any)
open import Data.List.Relation.Unary.First.Properties public
  using (All⇒¬First)
  renaming (cofirst? to first?)

open import Data.Nat.Base public
  using (ℕ; zero; suc; _+_; _≤_; _<_; s<s)
open import Data.Nat.Induction public
  using (<-wellFounded)
open import Data.Nat.Properties public
  using (+-identityʳ;
         ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
         n<1+n; 0<1+n; <⇒≤; +-monoˡ-<; +-monoʳ-<;
         +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)

open import Data.Product.Base public
  using (∃-syntax; _×_; -,_; _,_; uncurry; proj₁; proj₂)
  renaming (map to map-×; map₁ to map-×₁; map₂ to map-×₂)
open import Data.Product.Relation.Binary.Lex.Strict public
  using (×-Lex; ×-wellFounded)

open import Data.Sum.Base public
  using (_⊎_; inj₁; inj₂; [_,_])
  renaming (map to map-⊎)

open import Function.Base public
  using (id; _∘_; flip; _on_)

open import Function.Bundles public
  using (_⇔_; mk⇔)

open import Induction.WellFounded public
  using (WellFounded; Acc; acc)

open import Relation.Binary.Construct.On public
  using ()
  renaming (wellFounded to on-wellFounded)

open import Relation.Binary.PropositionalEquality.Core public
  using (_≡_; _≢_; refl; sym; ≢-sym; trans; cong; cong₂)

open import Relation.Nullary.Decidable public
  using (Dec; yes; no; ¬?; _⊎-dec_; _×-dec_)
  renaming (map to mapDec; map′ to mapDec′)

open import Relation.Nullary.Negation.Core public
  using (¬_; contradiction; contraposition)

-- extra lemmas

module _ where
  open import Data.Empty using (⊥-elim)
  open import Data.Fin.Properties using (∀-cons)
  open import Data.List.Relation.Unary.First using ([_])
  open import Relation.Unary using (Pred; ∁; _⊆_; Decidable)
  open import Relation.Nullary.Decidable.Core using (toSum)

  ¬First⇒¬Any : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
    → ∁ Q ⊆ P
    → ∁ (First P Q) ⊆ ∁ (Any Q)
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (here qx) = ¬pqxxs [ qx ]
  ¬First⇒¬Any ¬q⇒p ¬pqxxs (there qxs) =
    ¬First⇒¬Any ¬q⇒p (¬pqxxs ∘ (¬q⇒p (¬pqxxs ∘ [_]) ∷_)) qxs

  allOrCounterexample : ∀ {p n} {P : Fin n → Set p}
    → Decidable P
    → (∀ x → P x) ⊎ (∃[ x ] ¬ P x)
  allOrCounterexample {n = zero} P? = inj₁ (⊥-elim ∘ ¬Fin0)
  allOrCounterexample {n = suc n} P? with P? zero
  ... | no ¬P0 = inj₂ (zero , ¬P0)
  ... | yes P0 =
        map-⊎ (∀-cons P0) (map-× suc id) (allOrCounterexample (P? ∘ suc))
