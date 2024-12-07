module Pattern where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Subset as Subset using (Subset; _∉_; ⊥; ⁅_⁆; _∪_; ⋃; _─_; Nonempty)
open import Data.Fin.Subset.Properties as Subset using (x∈p∪q⁺; x∉⁅y⁆⇒x≢y; x∈∁p⇒x∉p; nonempty?)
open import Data.Fin.Properties using (any?)
open import Data.List as List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using (++⁺; ++⁻ˡ; ++⁻ʳ; ++⁻)
open import Data.List.Relation.Unary.First as First using (First; _∷_)
open import Data.List.Relation.Unary.First.Properties as First using (cofirst?; All⇒¬First)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Product using (∃-syntax; _×_; _,_; uncurry; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (id; _∘_; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; ≢-sym)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _×-dec_; _⊎-dec_; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)
open import Relation.Unary using (Pred; ∁; _⊆_)

infixr 6 _∣_
infixr 5 _∷_
infix 4 _≼_ _≼*_ _⋠_ _⋠*_ _≼?_ _≼*?_

--------------------------------------------------------------------------------
-- Types, values and patterns

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

  ConSet : Set
  ConSet = Subset numCons

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

inhabOf : Con α → Val α
inhabOf c = con c (All.tabulate λ {α} _ → inhab α)

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
∙* {[]} = []
∙* {_ ∷ _} = ∙ ∷ ∙*

rootCons : Pat α → ConSet α
rootCons ∙ = ⊥
rootCons (con c _) = ⁅ c ⁆
rootCons (p ∣ q) = rootCons p ∪ rootCons q

--------------------------------------------------------------------------------
-- Instance relation

data _≼_ {α} : Pat α → Val α → Set
data _≼*_ : Pats αs → Vals αs → Set

data _≼_ {α} where
  ∙≼ : ∀ {v} → ∙ ≼ v
  con≼ : ∀ {c ps vs} → ps ≼* vs → con c ps ≼ con c vs
  ∣≼ˡ : ∀ {p q v} → p ≼ v → p ∣ q ≼ v
  ∣≼ʳ : ∀ {p q v} → q ≼ v → p ∣ q ≼ v

data _≼*_ where
  [] : [] ≼* []
  _∷_ : ∀ {p : Pat α} {ps : Pats αs} {v vs}
    → p ≼ v
    → ps ≼* vs
    → p ∷ ps ≼* v ∷ vs

_⋠_ : Pat α → Val α → Set
p ⋠ v = ¬ p ≼ v

_⋠*_ : Pats αs → Vals αs → Set
ps ⋠* vs = ¬ ps ≼* vs

--------------------------------------------------------------------------------
-- Lemmas about the instance relation

∙*≼ : {vs : Vals αs} → ∙* ≼* vs
∙*≼ {vs = []} = []
∙*≼ {vs = _ ∷ _} = ∙≼ ∷ ∙*≼

module _ {p q : Pat α} {v} where

  ∣≼⁻ : p ∣ q ≼ v → p ≼ v ⊎ q ≼ v
  ∣≼⁻ (∣≼ˡ h) = inj₁ h
  ∣≼⁻ (∣≼ʳ h) = inj₂ h

  ∣≼⇔ : (p ≼ v ⊎ q ≼ v) ⇔ p ∣ q ≼ v
  ∣≼⇔ = mk⇔ [ ∣≼ˡ , ∣≼ʳ ] ∣≼⁻


module _ {c} {ps : Pats (args α c)} {vs} where

  con≼⁻ : con {α} c ps ≼ con c vs → ps ≼* vs
  con≼⁻ (con≼ h) = h

  con≼⇔ : ps ≼* vs ⇔ con {α} c ps ≼ con c vs
  con≼⇔ = mk⇔ con≼ con≼⁻


module _ {p : Pat α} {ps : Pats αs} {v vs} where

  ∷⁻ : p ∷ ps ≼* v ∷ vs → p ≼ v × ps ≼* vs
  ∷⁻ (h ∷ hs) = h , hs

  ∷⇔ : (p ≼ v × ps ≼* vs) ⇔ p ∷ ps ≼* v ∷ vs
  ∷⇔ = mk⇔ (uncurry _∷_) ∷⁻


++≼⁺ : ∀ {ps : Pats αs} {qs : Pats βs} {vs us}
  → ps ≼* vs
  → qs ≼* us
  → ++⁺ ps qs ≼* ++⁺ vs us
++≼⁺ [] qs≼us = qs≼us
++≼⁺ (p≼v ∷ ps≼vs) qs≼us = p≼v ∷ ++≼⁺ ps≼vs qs≼us

++≼⁻ : ∀ (ps : Pats αs) {qs : Pats βs} {vs us}
  → ++⁺ ps qs ≼* ++⁺ vs us
  → ps ≼* vs × qs ≼* us
++≼⁻ [] {vs = []} qs≼us = [] , qs≼us
++≼⁻ (p ∷ ps) {vs = v ∷ vs} (p≼v ∷ psqs≼vsus) =
  Product.map₁ (p≼v ∷_) (++≼⁻ ps psqs≼vsus)

++≼⇔ : ∀ {ps : Pats αs} {qs : Pats βs} {vs us}
  → (ps ≼* vs × qs ≼* us) ⇔ ++⁺ ps qs ≼* ++⁺ vs us
++≼⇔ = mk⇔ (uncurry ++≼⁺) (++≼⁻ _)

split≼ : ∀ (ps : Pats αs) {qs : Pats βs} {us}
  → ++⁺ ps qs ≼* us
  → ∃[ vs ] ∃[ ws ] ((++⁺ vs ws ≡ us) × (ps ≼* vs) × (qs ≼* ws))
split≼ [] {us = us} qs≼us = [] , us , refl , [] , qs≼us
split≼ (p ∷ ps) {us = u ∷ us} (p≼u ∷ ps≼us) =
  let vs , ws , p1 , p2 , p3 = split≼ ps {us = us} ps≼us
   in u ∷ vs , ws , cong (u ∷_) p1 , p≼u ∷ p2 , p3

module _ {ps : Pats αs} {u : Val β} {us : Vals βs} {vs} where

  ∙≼*⁺ : ++⁺ ∙* ps ≼* ++⁺ us vs → ∙ ∷ ps ≼* u ∷ vs
  ∙≼*⁺ ∙*ps≼usvs =
    let _ , ps≼vs = ++≼⁻ ∙* ∙*ps≼usvs in
    ∙≼ ∷ ps≼vs

  ∙≼*⁻ : ∙ ∷ ps ≼* u ∷ vs → ++⁺ ∙* ps ≼* ++⁺ us vs
  ∙≼*⁻ (∙≼ ∷ ps≼vs) = ++≼⁺ ∙*≼ ps≼vs

  ∙≼*⇔ : (++⁺ ∙* ps ≼* ++⁺ us vs) ⇔ (∙ ∷ ps ≼* u ∷ vs)
  ∙≼*⇔ = mk⇔ ∙≼*⁺ ∙≼*⁻


module _ {p q : Pat α} {ps : Pats αs} {v vs} where

  ∣≼*⁺ : (p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs) → p ∣ q ∷ ps ≼* v ∷ vs
  ∣≼*⁺ (inj₁ (p≼v ∷ ps≼vs)) = ∣≼ˡ p≼v ∷ ps≼vs
  ∣≼*⁺ (inj₂ (q≼v ∷ ps≼vs)) = ∣≼ʳ q≼v ∷ ps≼vs

  ∣≼*⁻ : p ∣ q ∷ ps ≼* v ∷ vs → p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs
  ∣≼*⁻ (∣≼ˡ p≼v ∷ ps≼vs) = inj₁ (p≼v ∷ ps≼vs)
  ∣≼*⁻ (∣≼ʳ q≼v ∷ ps≼vs) = inj₂ (q≼v ∷ ps≼vs)

  ∣≼*⇔ : (p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs) ⇔ (p ∣ q ∷ ps ≼* v ∷ vs)
  ∣≼*⇔ = mk⇔ ∣≼*⁺ ∣≼*⁻


module _ {c} {rs : Pats (args α c)} {ps : Pats αs} {us vs} where

  con≼*⁺ : (++⁺ rs ps ≼* ++⁺ us vs) → con {α} c rs ∷ ps ≼* con c us ∷ vs
  con≼*⁺ rsps≼usvs =
    let rs≼us , ps≼vs = ++≼⁻ rs rsps≼usvs in
    con≼ rs≼us ∷ ps≼vs

  con≼*⁻ : con {α} c rs ∷ ps ≼* con c us ∷ vs → ++⁺ rs ps ≼* ++⁺ us vs
  con≼*⁻ (con≼ rs≼us ∷ ps≼vs) = ++≼⁺ rs≼us ps≼vs

  con≼*⇔ : (++⁺ rs ps ≼* ++⁺ us vs) ⇔ (con {α} c rs ∷ ps ≼* con c us ∷ vs)
  con≼*⇔ = mk⇔ con≼*⁺ con≼*⁻


c≢d→c⋠d : ∀ {c d} {ps : Pats (args α c)} {vs : Vals (args α d)}
  → c ≢ d
  → con {α} c ps ⋠ con d vs
c≢d→c⋠d c≢c (con≼ _) = c≢c refl

--------------------------------------------------------------------------------
-- Pattern matching

_≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
_≼*?_ : (ps : Pats αs) (vs : Vals αs) → Dec (ps ≼* vs)

∙ ≼? v = yes ∙≼
con c ps ≼? con d vs with c Fin.≟ d
... | yes refl = Dec.map con≼⇔ (ps ≼*? vs)
... | no c≢d = no (c≢d→c⋠d c≢d)
p ∣ q ≼? v = Dec.map ∣≼⇔ ((p ≼? v) ⊎-dec (q ≼? v))

[] ≼*? [] = yes []
p ∷ ps ≼*? v ∷ vs = Dec.map ∷⇔ ((p ≼? v) ×-dec (ps ≼*? vs))

-- First match
Match : Vals αs → List (Pats αs) → Set
Match vs = First (_⋠* vs) (_≼* vs)

match? : (vs : Vals αs) (pss : List (Pats αs)) → Dec (Match vs pss)
match? vs = cofirst? (_≼*? vs)

--------------------------------------------------------------------------------
-- Exhaustiveness and usefulness

Exhaustive : List (Pats αs) → Set
Exhaustive pss = ∀ vs → Match vs pss

NonExhaustive : List (Pats αs) → Set
NonExhaustive pss = ∃[ vs ] ¬ Match vs pss

Useful : Pats αs → List (Pats αs) → Set
Useful ps pss = ∃[ vs ] ps ≼* vs × All (_⋠* vs) pss

NonExhaustive′ : List (Pats αs) → Set
NonExhaustive′ = Useful ∙*

Exhaustive′ : List (Pats αs) → Set
Exhaustive′ pss = ¬ NonExhaustive′ pss

¬First⇒All : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
  → ∁ Q ⊆ P
  → ∁ (First P Q) ⊆ All P
¬First⇒All ¬q⇒p {[]} _ = []
¬First⇒All ¬q⇒p {x ∷ xs} ¬pqxxs =
  let px = ¬q⇒p (¬pqxxs ∘ First.[_]) in
  px ∷ ¬First⇒All ¬q⇒p (¬pqxxs ∘ (px ∷_))

module _ {pss : List (Pats αs)} where

  NonExhaustive′→NonExhaustive : NonExhaustive′ pss → NonExhaustive pss
  NonExhaustive′→NonExhaustive (vs , _ , ∙*ps⋠vs) = vs , All⇒¬First id ∙*ps⋠vs

  NonExhaustive→NonExhaustive′ : NonExhaustive pss → NonExhaustive′ pss
  NonExhaustive→NonExhaustive′ (vs , pss⋠vs) = vs , ∙*≼ , ¬First⇒All id pss⋠vs

  NonExhaustive′⇔NonExhaustive : NonExhaustive′ pss ⇔ NonExhaustive pss
  NonExhaustive′⇔NonExhaustive = mk⇔ NonExhaustive′→NonExhaustive NonExhaustive→NonExhaustive′

  Exhaustive→Exhaustive′ : Exhaustive pss → Exhaustive′ pss
  Exhaustive→Exhaustive′ exh (vs , _ , pss⋠vs) = All⇒¬First id pss⋠vs (exh vs)

  Exhaustive′→Exhaustive : Exhaustive′ pss → Exhaustive pss
  Exhaustive′→Exhaustive exh vs with match? vs pss
  ... | yes pss≼vs = pss≼vs
  ... | no pss⋠vs = contradiction (vs , ∙*≼ , ¬First⇒All id pss⋠vs) exh

  Exhaustive′⇔Exhaustive : Exhaustive′ pss ⇔ Exhaustive pss
  Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

--------------------------------------------------------------------------------

𝒮-aux : ∀ c → Pats (α ∷ αs) → List (Pats (args α c ++ αs))
𝒮-aux c (∙ ∷ ps) = ++⁺ ∙* ps ∷ []
𝒮-aux c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = ++⁺ rs ps ∷ []
𝒮-aux c (r₁ ∣ r₂ ∷ ps) = 𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)

𝒮 : ∀ c → List (Pats (α ∷ αs)) → List (Pats (args α c ++ αs))
𝒮 = concatMap ∘ 𝒮-aux

𝒟-aux : Pats (α ∷ αs) → List (Pats αs)
𝒟-aux (∙ ∷ ps) = ps ∷ []
𝒟-aux (con _ _ ∷ ps) = []
𝒟-aux (r₁ ∣ r₂ ∷ ps) = 𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps)

𝒟 : List (Pats (α ∷ αs)) → List (Pats αs)
𝒟 = concatMap 𝒟-aux

--------------------------------------------------------------------------------

≟-refl : ∀ {n} (i : Fin n) → (i Fin.≟ i) ≡ yes refl
≟-refl i with i Fin.≟ i
... | yes refl = refl
... | no ¬refl = contradiction refl ¬refl

useful-[]-[] : Useful [] []
useful-[]-[] = [] , [] , []

¬useful-[]-∷ : ∀ {ps pss} → ¬ Useful [] (ps ∷ pss)
¬useful-[]-∷ {ps = []} ([] , _ , ¬[] ∷ _) = ¬[] []

module _ {r₁ r₂ : Pat α} {ps : Pats αs} {pss} where

  useful-∣⁺ : Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss → Useful (r₁ ∣ r₂ ∷ ps) pss
  useful-∣⁺ (inj₁ (vvs , r₁≼v ∷ ps≼vs , pss⋠vvs)) =
    vvs , ∣≼ˡ r₁≼v ∷ ps≼vs , pss⋠vvs
  useful-∣⁺ (inj₂ (vvs , r₂≼v ∷ ps≼vs , pss⋠vvs)) =
    vvs , ∣≼ʳ r₂≼v ∷ ps≼vs , pss⋠vvs

  useful-∣⁻ : Useful (r₁ ∣ r₂ ∷ ps) pss → Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss
  useful-∣⁻ (vvs , ∣≼ˡ r₁≼v ∷ ps≼vs , pss⋠vvs) =
    inj₁ (vvs , r₁≼v ∷ ps≼vs , pss⋠vvs)
  useful-∣⁻ (vvs , ∣≼ʳ r₂≼v ∷ ps≼vs , pss⋠vvs) =
    inj₂ (vvs , r₂≼v ∷ ps≼vs , pss⋠vvs)

  useful-∣⇔ : (Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss) ⇔ Useful (r₁ ∣ r₂ ∷ ps) pss
  useful-∣⇔ = mk⇔ useful-∣⁺ useful-∣⁻


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  𝒮-aux-pres-⋠ : ∀ {ps}
    → ps ⋠* con {α} c us ∷ vs
    → All (_⋠* ++⁺ us vs) (𝒮-aux c ps)
  𝒮-aux-pres-⋠ {∙ ∷ ps} ∙ps⋠cusvs = contraposition ∙≼*⁺ ∙ps⋠cusvs ∷ []
  𝒮-aux-pres-⋠ {con d rs ∷ ps} drsps⋠cusvs with c Fin.≟ d
  ... | no _ = []
  ... | yes refl = contraposition con≼*⁺ drsps⋠cusvs ∷ []
  𝒮-aux-pres-⋠ {r₁ ∣ r₂ ∷ ps} r₁₂ps⋠cusvs =
    ++⁺
      (𝒮-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₁) r₁₂ps⋠cusvs))
      (𝒮-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₂) r₁₂ps⋠cusvs))

  𝒮-pres-⋠ : ∀ {pss}
    → All (_⋠* con c us ∷ vs) pss
    → All (_⋠* ++⁺ us vs) (𝒮 c pss)
  𝒮-pres-⋠ = All.concat⁺ ∘ All.gmap⁺ 𝒮-aux-pres-⋠

  𝒮-aux-pres-⋠⁻ : ∀ {ps}
    → All (_⋠* ++⁺ us vs) (𝒮-aux c ps)
    → ps ⋠* con {α} c us ∷ vs
  𝒮-aux-pres-⋠⁻ {∙ ∷ ps} (∙*ps⋠usvs ∷ []) (∙≼ ∷ ps≼vs) =
    ∙*ps⋠usvs (++≼⁺ ∙*≼ ps≼vs)
  𝒮-aux-pres-⋠⁻ {con c rs ∷ ps} 𝒮rsps⋠usvs (con≼ rs≼us ∷ ps≼vs) with c Fin.≟ c | ≟-refl c
  𝒮-aux-pres-⋠⁻ {con c rs ∷ ps} (rsps⋠usvs ∷ []) (con≼ rs≼us ∷ ps≼vs) | _ | refl =
    rsps⋠usvs (++≼⁺ rs≼us ps≼vs)
  𝒮-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} 𝒮r₁ps𝒮r₂ps⋠usvs (∣≼ˡ r₁≼cus ∷ ps≼vs) =
    𝒮-aux-pres-⋠⁻ (++⁻ˡ _ 𝒮r₁ps𝒮r₂ps⋠usvs) (r₁≼cus ∷ ps≼vs)
  𝒮-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} 𝒮r₁ps𝒮r₂ps⋠usvs (∣≼ʳ r₂≼cus ∷ ps≼vs) =
    𝒮-aux-pres-⋠⁻ (++⁻ʳ _ 𝒮r₁ps𝒮r₂ps⋠usvs) (r₂≼cus ∷ ps≼vs)

  𝒮-pres-⋠⁻ : ∀ {pss}
    → All (_⋠* ++⁺ us vs) (𝒮 c pss)
    → All (_⋠* con c us ∷ vs) pss
  𝒮-pres-⋠⁻ = All.gmap⁻ 𝒮-aux-pres-⋠⁻ ∘ All.concat⁻

  𝒮-pres-⋠⇔ : ∀ {pss}
    → All (_⋠* ++⁺ us vs) (𝒮 c pss) ⇔ All (_⋠* con c us ∷ vs) pss
  𝒮-pres-⋠⇔ = mk⇔ 𝒮-pres-⋠⁻ 𝒮-pres-⋠


module _ {c} {rs : Pats (args α c)} {ps : Pats αs} {pss : List (Pats (α ∷ αs))} where

  useful-con⁺ : Useful (++⁺ rs ps) (𝒮 c pss) → Useful (con c rs ∷ ps) pss
  useful-con⁺ (usvs , rsps≼usvs , 𝒮pss⋠usvs)
    with us , vs , refl , rs≼us , ps≼vs ← split≼ rs rsps≼usvs =
    con c us ∷ vs , con≼ rs≼us ∷ ps≼vs , 𝒮-pres-⋠⁻ 𝒮pss⋠usvs

  useful-con⁻ : Useful (con c rs ∷ ps) pss → Useful (++⁺ rs ps) (𝒮 c pss)
  useful-con⁻ (con c vs ∷ us , con≼ rs≼vs ∷ ps≼us , pss⋠cvsus) =
    ++⁺ vs us , ++≼⁺ rs≼vs ps≼us , 𝒮-pres-⋠ pss⋠cvsus

  useful-con⇔ : Useful (++⁺ rs ps) (𝒮 c pss) ⇔ Useful (con c rs ∷ ps) pss
  useful-con⇔ = mk⇔ useful-con⁺ useful-con⁻


module _ {v : Val α} {vs : Vals αs} where

  𝒟-aux-pres-⋠ : ∀ {ps} → ps ⋠* v ∷ vs → All (_⋠* vs) (𝒟-aux ps)
  𝒟-aux-pres-⋠ {∙ ∷ ps} ∙ps⋠vvs =
    contraposition (∙≼ ∷_) ∙ps⋠vvs ∷ []
  𝒟-aux-pres-⋠ {con _ _ ∷ ps} _ = []
  𝒟-aux-pres-⋠ {r₁ ∣ r₂ ∷ ps} r₁₂ps⋠vvs =
    ++⁺
      (𝒟-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₁) r₁₂ps⋠vvs))
      (𝒟-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₂) r₁₂ps⋠vvs))

  𝒟-pres-⋠ : ∀ {pss} → All (_⋠* v ∷ vs) pss → All (_⋠* vs) (𝒟 pss)
  𝒟-pres-⋠ = All.concat⁺ ∘ All.gmap⁺ 𝒟-aux-pres-⋠


module _ {n} {x : Fin n} {p q} where

  x∉p∪q⁻ˡ : x ∉ p ∪ q → x ∉ p
  x∉p∪q⁻ˡ = contraposition (x∈p∪q⁺ ∘ inj₁)

  x∉p∪q⁻ʳ : x ∉ p ∪ q → x ∉ q
  x∉p∪q⁻ʳ = contraposition (x∈p∪q⁺ ∘ inj₂)

  x∉p∪q⁻ : x ∉ p ∪ q → x ∉ p × x ∉ q
  x∉p∪q⁻ x∉p∪q = x∉p∪q⁻ˡ x∉p∪q , x∉p∪q⁻ʳ x∉p∪q


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  c∉ps→𝒟-aux-pres-⋠⁻ : ∀ {ps}
    → c ∉ rootCons (All.head ps)
    → All (_⋠* vs) (𝒟-aux ps)
    → ps ⋠* con {α} c us ∷ vs
  c∉ps→𝒟-aux-pres-⋠⁻ {∙ ∷ ps} c∉ps (ps⋠vs ∷ []) (∙≼ ∷ ps≼vs) = ps⋠vs ps≼vs
  c∉ps→𝒟-aux-pres-⋠⁻ {con d _ ∷ ps} c∉⁅d⁆ [] (d≼c ∷ ps≼vs) =
    c≢d→c⋠d (≢-sym (x∉⁅y⁆⇒x≢y c∉⁅d⁆)) d≼c
  c∉ps→𝒟-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ 𝒟r₁ps𝒟r₂ps⋠vs (∣≼ˡ r₁≼cus ∷ ps≼vs) =
    c∉ps→𝒟-aux-pres-⋠⁻ (x∉p∪q⁻ˡ c∉r₁∪r₂) (++⁻ˡ _  𝒟r₁ps𝒟r₂ps⋠vs) (r₁≼cus ∷ ps≼vs)
  c∉ps→𝒟-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ 𝒟r₁ps𝒟r₂ps⋠vs (∣≼ʳ r₂≼cus ∷ ps≼vs) =
    c∉ps→𝒟-aux-pres-⋠⁻ (x∉p∪q⁻ʳ c∉r₁∪r₂) (++⁻ʳ _  𝒟r₁ps𝒟r₂ps⋠vs) (r₂≼cus ∷ ps≼vs)

  c∉pss→𝒟-pres-⋠⁻ : ∀ {pss}
    → c ∉ ⋃ (List.map (rootCons ∘ All.head) pss)
    → All (_⋠* vs) (𝒟 pss)
    → All (_⋠* con {α} c us ∷ vs) pss
  c∉pss→𝒟-pres-⋠⁻ {[]} c∉pss [] = []
  c∉pss→𝒟-pres-⋠⁻ {ps ∷ pss} c∉ps∪pss 𝒟ps𝒟pss⋠vs =
    let 𝒟ps⋠vs , 𝒟pss⋠vs = ++⁻ (𝒟-aux ps) 𝒟ps𝒟pss⋠vs
        c∉ps , c∉pss = x∉p∪q⁻ c∉ps∪pss
     in c∉ps→𝒟-aux-pres-⋠⁻ c∉ps 𝒟ps⋠vs ∷ c∉pss→𝒟-pres-⋠⁻ c∉pss 𝒟pss⋠vs


module _ {α} {ps : Pats αs} {pss} where

  useful-∙-𝒟⁺ :
      Nonempty (Subset.∁ (⋃ (List.map (rootCons ∘ All.head) pss)))
    → Useful ps (𝒟 pss)
    → Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒟⁺ (c , c∈∁pss) (vs , ps≼vs , 𝒟pss⋠vs) =
    inhabOf c ∷ vs , ∙≼ ∷ ps≼vs , c∉pss→𝒟-pres-⋠⁻ (x∈∁p⇒x∉p c∈∁pss) 𝒟pss⋠vs

  useful-∙-𝒟⁻ : Useful (∙ {α} ∷ ps) pss → Useful ps (𝒟 pss)
  useful-∙-𝒟⁻ (v ∷ vs , ∙≼ ∷ ps≼vs , pss⋠vvs) = vs , ps≼vs , 𝒟-pres-⋠ pss⋠vvs


module _ {α αs} {ps : Pats αs} {pss} where

  useful-∙-𝒮⁺ : ∃[ c ] Useful (++⁺ ∙* ps) (𝒮 c pss) → Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒮⁺ (c , usvs , ∙*ps≼usvs , 𝒮pss⋠usvs)
    with us , vs , refl , _ , ps≼vs ← split≼ {args α c} ∙* ∙*ps≼usvs =
    con c us ∷ vs , ∙≼ ∷ ps≼vs , 𝒮-pres-⋠⁻ 𝒮pss⋠usvs

  useful-∙-𝒮⁻ : Useful (∙ {α} ∷ ps) pss → ∃[ c ] Useful (++⁺ ∙* ps) (𝒮 c pss)
  useful-∙-𝒮⁻ (con c us ∷ vs , ∙≼ ∷ ps≼vs , pss⋠cusvs) =
    c , ++⁺ us vs , ++≼⁺ ∙*≼ ps≼vs , 𝒮-pres-⋠ pss⋠cusvs

  useful-∙-𝒮⇔ : (∃[ c ] Useful (++⁺ ∙* ps) (𝒮 c pss)) ⇔ Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒮⇔ = mk⇔ useful-∙-𝒮⁺ useful-∙-𝒮⁻

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

{-# TERMINATING #-}
useful? : (ps : Pats αs) (pss : List (Pats αs)) → Dec (Useful ps pss)
useful? [] [] = yes useful-[]-[]
useful? [] (_ ∷ _) = no ¬useful-[]-∷
useful? (_∷_ {α} ∙ ps) pss with nonempty? (Subset.∁ (⋃ (List.map (rootCons ∘ All.head) pss)))
... | yes ∃c∈∁pss =
      Dec.map′ (useful-∙-𝒟⁺ ∃c∈∁pss) useful-∙-𝒟⁻ (useful? ps (𝒟 pss))
... | no _ =
      Dec.map useful-∙-𝒮⇔ (any? λ c → useful? (++⁺ ∙* ps) (𝒮 c pss))
useful? (con c rs ∷ ps) pss =
  Dec.map useful-con⇔ (useful? (++⁺ rs ps) (𝒮 c pss))
useful? (r₁ ∣ r₂ ∷ ps) pss =
  Dec.map useful-∣⇔ (useful? (r₁ ∷ ps) pss ⊎-dec useful? (r₂ ∷ ps) pss)

exhaustive? : (pss : List (Pats αs)) → Exhaustive pss ⊎ NonExhaustive pss
exhaustive? pss with useful? ∙* pss
... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
... | no h = inj₁ (Exhaustive′→Exhaustive h)

--------------------------------------------------------------------------------

nat : Ty
nat .numCons = 2
nat .args zero = []
nat .args (suc zero) = nat ∷ []
nat .inhabCon = zero
nat .inhabArgs = []

pattern zero′ = con zero []
pattern suc′ n = con (suc zero) (n ∷ [])

patmat₁ : List (Pats (nat ∷ nat ∷ []))
patmat₁ =
  (zero′ ∷ zero′ ∷ []) ∷
  (suc′ ∙ ∷ zero′ ∷ []) ∷
  (zero′ ∷ suc′ ∙ ∷ []) ∷
  []

patmat₂ : List (Pats (nat ∷ nat ∷ []))
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
