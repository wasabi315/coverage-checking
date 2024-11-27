module Pattern where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.First as First using (First; _∷_)
open import Data.List.Relation.Unary.First.Properties as First using (cofirst?; All⇒¬First)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (id; _∘_; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _×-dec_; _⊎-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction)

infixr 6 _∣_
infixr 5 _∷_
infix  4 _≼_ _≼*_ _≼?_ _≼*?_

--------------------------------------------------------------------------------

record Ty : Set
data Val (α : Ty) : Set
Vals : List Ty → Set

record Ty where
  coinductive
  field
    numCons : ℕ
    args : Fin numCons → List Ty
    inhabCon : Fin numCons
    inhabArgs : Vals (args inhabCon)

  Con : Set
  Con = Fin numCons

open Ty public

private
  variable
    α β : Ty
    αs βs : List Ty

data Val α where
  con : ∀ c → Vals (args α c) → Val α

Vals = All Val

-- All types are inhabited
inhab : ∀ α → Val α
inhab α = con (inhabCon α) (inhabArgs α)

--------------------------------------------------------------------------------

data Pat (α : Ty) : Set
Pats : List Ty → Set

data Pat α where
  -- Wildcard pattern
  ∙ : Pat α
  -- Constructor pattern
  con : ∀ c → Pats (args α c) → Pat α
  -- Or pattern
  _∣_ : Pat α → Pat α → Pat α

Pats = All Pat

∙* : Pats αs
∙* {αs = []} = []
∙* {αs = _ ∷ _} = ∙ ∷ ∙*

--------------------------------------------------------------------------------

data _≼_ {α} : Pat α → Val α → Set
data _≼*_ : Pats αs → Vals αs → Set

data _≼_ {α} where
  ∙≼ : ∀ {v}
    → ∙ ≼ v
  c≼c : ∀ {c ps vs}
    → ps ≼* vs
    → con c ps ≼ con c vs
  ∣≼ₗ : ∀ {p q v}
    → p ≼ v
    → (p ∣ q) ≼ v
  ∣≼ᵣ : ∀ {p q v}
    → q ≼ v
    → (p ∣ q) ≼ v

data _≼*_ where
  [] : [] ≼* []
  _∷_ : ∀ {p : Pat α} {ps : Pats αs} {v vs}
    → p ≼ v
    → ps ≼* vs
    → p ∷ ps ≼* v ∷ vs

∙*≼ : {vs : Vals αs} → ∙* ≼* vs
∙*≼ {vs = []} = []
∙*≼ {vs = v ∷ vs} = ∙≼ ∷ ∙*≼

--------------------------------------------------------------------------------

∣≼-inv : ∀ {p q : Pat α} {v} → (p ∣ q) ≼ v → (p ≼ v) ⊎ (q ≼ v)
∣≼-inv (∣≼ₗ h) = inj₁ h
∣≼-inv (∣≼ᵣ h) = inj₂ h

∣≼-equiv : ∀ {p q : Pat α} {v} → (p ≼ v ⊎ q ≼ v) ⇔ (p ∣ q) ≼ v
∣≼-equiv = mk⇔ [ ∣≼ₗ , ∣≼ᵣ ] ∣≼-inv

c≼c-inv : ∀ {c} {ps : Pats (args α c)} {vs}
  → con {α} c ps ≼ con c vs
  → ps ≼* vs
c≼c-inv (c≼c h) = h

c≼c-equiv : ∀ {c} {ps : Pats (args α c)} {vs}
  → ps ≼* vs ⇔ con {α} c ps ≼ con c vs
c≼c-equiv = mk⇔ c≼c c≼c-inv

∷-inv : ∀ {p : Pat α} {ps : Pats αs} {v vs}
  → p ∷ ps ≼* v ∷ vs
  → p ≼ v × ps ≼* vs
∷-inv (h ∷ hs) = h , hs

∷-equiv : ∀ {p : Pat α} {ps : Pats αs} {v vs}
  → (p ≼ v × ps ≼* vs) ⇔ p ∷ ps ≼* v ∷ vs
∷-equiv = mk⇔ (uncurry _∷_) ∷-inv

c≢d→¬c≼d : ∀ {c d} {ps : Pats (args α c)} {vs : Vals (args α d)}
  → c ≢ d
  → ¬ con {α} c ps ≼ con d vs
c≢d→¬c≼d h (c≼c _) = h refl

_≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
_≼*?_ : (ps : Pats αs) (vs : Vals αs) → Dec (ps ≼* vs)

∙ ≼? v = yes ∙≼
con c ps ≼? con d vs with c Fin.≟ d
... | yes refl = Dec.map c≼c-equiv (ps ≼*? vs)
... | no c≢d = no (c≢d→¬c≼d c≢d)
(p ∣ q) ≼? v = Dec.map ∣≼-equiv ((p ≼? v) ⊎-dec (q ≼? v))

[] ≼*? [] = yes []
(p ∷ ps) ≼*? (v ∷ vs) = Dec.map ∷-equiv ((p ≼? v) ×-dec (ps ≼*? vs))

Match : Vals αs → List (Pats αs) → Set
Match vs pss = First (λ ps → ¬ ps ≼* vs) (_≼* vs) pss

match? : (vs : Vals αs) (pss : List (Pats αs)) → Dec (Match vs pss)
match? vs = cofirst? (_≼*? vs)

--------------------------------------------------------------------------------

Useful : Pats αs → List (Pats αs) → Set
Useful ps pss = ∃[ vs ] (ps ≼* vs) × All (λ ps → ¬ ps ≼* vs) pss

Exhaustive : List (Pats αs) → Set
Exhaustive pss = ∀ vs → Match vs pss

Exhaustive′ : List (Pats αs) → Set
Exhaustive′ pss = ¬ Useful ∙* pss

¬First⇒All¬ : ∀ {a p} {A : Set a} {P : A → Set p} {xs}
  → ¬ First (¬_ ∘ P) P xs
  → All (¬_ ∘ P) xs
¬First⇒All¬ {xs = []} h = []
¬First⇒All¬ {xs = x ∷ xs} h = h' ∷ ¬First⇒All¬ (h ∘ (h' ∷_))
  where
    h' = h ∘ First.[_]

Exhaustive→Exhaustive′ : {pss : List (Pats αs)}
  → Exhaustive pss
  → Exhaustive′ pss
Exhaustive→Exhaustive′ exh (vs , _ , ¬pss≼vs) = All⇒¬First id ¬pss≼vs (exh vs)

Exhaustive′→Exhaustive : {pss : List (Pats αs)}
  → Exhaustive′ pss
  → Exhaustive pss
Exhaustive′→Exhaustive {pss = pss} exh vs with match? vs pss
... | yes pss≼vs = pss≼vs
... | no ¬pss≼vs = contradiction (vs , ∙*≼ , ¬First⇒All¬ ¬pss≼vs) exh

Exhaustive⇔Exhaustive′ : {pss : List (Pats αs)}
  → Exhaustive pss ⇔ Exhaustive′ pss
Exhaustive⇔Exhaustive′ = mk⇔ Exhaustive→Exhaustive′ Exhaustive′→Exhaustive

--------------------------------------------------------------------------------

nat : Ty
nat .numCons = 2
nat .args zero = []
nat .args (suc zero) = nat ∷ []
nat .inhabCon = zero
nat .inhabArgs = []

pattern zero′ = con zero []
pattern suc′ n = con (suc zero) (n ∷ [])

patmat : List (Pats (nat ∷ nat ∷ []))
patmat =
  (zero′ ∷ zero′ ∷ []) ∷
  (suc′ ∙ ∷ zero′ ∷ []) ∷
  (zero′ ∷ suc′ ∙ ∷ []) ∷
  []

vals₁ : Vals (nat ∷ nat ∷ [])
vals₁ = suc′ zero′ ∷ suc′ zero′ ∷ []

vals₂ : Vals (nat ∷ nat ∷ [])
vals₂ = suc′ zero′ ∷ zero′ ∷ []

_ : match? vals₁ patmat ≡ no _
_ = refl

_ : match? vals₂ patmat ≡ yes _
_ = refl
