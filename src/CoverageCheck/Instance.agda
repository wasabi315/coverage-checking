module CoverageCheck.Instance where

open import CoverageCheck.Prelude
open import CoverageCheck.Syntax

infixr 5 _∷_
infix 4 _≼_ _≼*_ _≼**_ _⋠_ _⋠*_ _⋠**_ _≼?_ _≼*?_

private
  variable
    α β : Ty
    αs βs : Tys

--------------------------------------------------------------------------------
-- Instance relation

data _≼_ {α : Ty} : Pat α → Val α → Set
data _≼*_ : Pats αs → Vals αs → Set

-- p ≼ v : pattern p matches value v
data _≼_ {α} where
  ∙≼ : {v : Val α} → ∙ ≼ v

  con≼ : {c : Con α} {ps : Pats (argsTy α c)} {vs : Vals (argsTy α c)}
    → ps ≼* vs
    → con c ps ≼ con c vs

  ∣≼ˡ : {p q : Pat α} {v : Val α}
    → p ≼ v
    → p ∣ q ≼ v

  ∣≼ʳ : {p q : Pat α} {v : Val α}
    → q ≼ v
    → p ∣ q ≼ v

-- ps ≼* vs : each pattern in ps matches the corresponding value in vs
data _≼*_ where
  [] : [] ≼* []

  _∷_ : {p : Pat α} {ps : Pats αs} {v : Val α} {vs : Vals αs}
    → p ≼ v
    → ps ≼* vs
    → p ∷ ps ≼* v ∷ vs

_≼**_ : PatMat αs → Vals αs → Set
P ≼** vs = Any (_≼* vs) P

_⋠_ : Pat α → Val α → Set
p ⋠ v = ¬ p ≼ v

_⋠*_ : Pats αs → Vals αs → Set
ps ⋠* vs = ¬ ps ≼* vs

_⋠**_ : PatMat αs → Vals αs → Set
P ⋠** vs = ¬ P ≼** vs

--------------------------------------------------------------------------------
-- Lemmas about the instance relation

-- ∙* matches any list of values
∙*≼ : {vs : Vals αs} → ∙* ≼* vs
∙*≼ {vs = []} = []
∙*≼ {vs = _ ∷ _} = ∙≼ ∷ ∙*≼

module _ {p q : Pat α} {v : Val α} where

  ∣≼⁻ : p ∣ q ≼ v → p ≼ v ⊎ q ≼ v
  ∣≼⁻ (∣≼ˡ h) = inj₁ h
  ∣≼⁻ (∣≼ʳ h) = inj₂ h

  -- p ∣ q ≼ v iff p ≼ v or q ≼ v
  ∣≼⇔ : (p ≼ v ⊎ q ≼ v) ⇔ p ∣ q ≼ v
  ∣≼⇔ = mk⇔ [ ∣≼ˡ , ∣≼ʳ ] ∣≼⁻


module _ {c : Con α} {ps : Pats (argsTy α c)} {vs : Vals (argsTy α c)} where

  con≼⁻ : con {α} c ps ≼ con c vs → ps ≼* vs
  con≼⁻ (con≼ h) = h

  -- con c ps ≼ con c vs iff ps ≼* vs
  con≼⇔ : ps ≼* vs ⇔ con {α} c ps ≼ con c vs
  con≼⇔ = mk⇔ con≼ con≼⁻


module _ {p : Pat α} {ps : Pats αs} {v : Val α} {vs : Vals αs} where

  ∷⁻ : p ∷ ps ≼* v ∷ vs → p ≼ v × ps ≼* vs
  ∷⁻ (h ∷ hs) = h , hs

  -- p ∷ ps ≼* v ∷ vs iff p ≼ v and ps ≼* vs
  ∷⇔ : (p ≼ v × ps ≼* vs) ⇔ p ∷ ps ≼* v ∷ vs
  ∷⇔ = mk⇔ (uncurry _∷_) ∷⁻


++⁺ : {ps : Pats αs} {qs : Pats βs} {vs : Vals αs} {us : Vals βs}
  → ps ≼* vs
  → qs ≼* us
  → (ps ++ₚ qs) ≼* (vs ++ᵥ us)
++⁺ [] qs≼us = qs≼us
++⁺ (p≼v ∷ ps≼vs) qs≼us = p≼v ∷ ++⁺ ps≼vs qs≼us

++⁻ : (ps : Pats αs) {qs : Pats βs} {vs : Vals αs} {us : Vals βs}
  → (ps ++ₚ qs) ≼* (vs ++ᵥ us)
  → (ps ≼* vs) × (qs ≼* us)
++⁻ [] {vs = []} qs≼us = [] , qs≼us
++⁻ (p ∷ ps) {vs = v ∷ vs} (p≼v ∷ psqs≼vsus) =
  map-×₁ (p≼v ∷_) (++⁻ ps psqs≼vsus)

-- (ps ++ qs) ≼* (vs ++ us) iff ps ≼* vs and qs ≼* us
++⇔ : {ps : Pats αs} {qs : Pats βs} {vs : Vals αs} {us : Vals βs}
  → (ps ≼* vs × qs ≼* us) ⇔ (ps ++ₚ qs) ≼* (vs ++ᵥ us)
++⇔ = mk⇔ (uncurry ++⁺) (++⁻ _)

split : (ps : Pats αs) {qs : Pats βs} {us : Vals (αs ++ βs)}
  → (ps ++ₚ qs) ≼* us
  → ∃[ vs ] ∃[ ws ] (vs ++ᵥ ws ≡ us) × (ps ≼* vs) × (qs ≼* ws)
split [] {us = us} qs≼us = [] , us , refl , [] , qs≼us
split (p ∷ ps) {us = u ∷ us} (p≼u ∷ ps≼us) =
  let vs , ws , p1 , p2 , p3 = split ps {us = us} ps≼us
   in u ∷ vs , ws , cong (u ∷_) p1 , p≼u ∷ p2 , p3

module _ {ps : Pats αs} {u : Val β} {us : Vals βs} {vs : Vals αs} where

  ∙≼*⁺ : (∙* ++ₚ ps) ≼* (us ++ᵥ vs) → ∙ ∷ ps ≼* u ∷ vs
  ∙≼*⁺ ∙*ps≼usvs =
    let _ , ps≼vs = ++⁻ ∙* ∙*ps≼usvs in
    ∙≼ ∷ ps≼vs

  ∙≼*⁻ : ∙ ∷ ps ≼* u ∷ vs → (∙* ++ₚ ps) ≼* (us ++ᵥ vs)
  ∙≼*⁻ (∙≼ ∷ ps≼vs) = ++⁺ ∙*≼ ps≼vs

  -- (∙ ∷ ps) ≼* (u ∷ vs) iff (∙* ++ ps) ≼* (us ++ vs)
  ∙≼*⇔ : (∙* ++ₚ ps) ≼* (us ++ᵥ vs) ⇔ (∙ ∷ ps) ≼* (u ∷ vs)
  ∙≼*⇔ = mk⇔ ∙≼*⁺ ∙≼*⁻


module _ {p q : Pat α} {ps : Pats αs} {v : Val α} {vs : Vals αs} where

  ∣≼*⁺ : (p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs) → p ∣ q ∷ ps ≼* v ∷ vs
  ∣≼*⁺ (inj₁ (p≼v ∷ ps≼vs)) = ∣≼ˡ p≼v ∷ ps≼vs
  ∣≼*⁺ (inj₂ (q≼v ∷ ps≼vs)) = ∣≼ʳ q≼v ∷ ps≼vs

  ∣≼*⁻ : p ∣ q ∷ ps ≼* v ∷ vs → p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs
  ∣≼*⁻ (∣≼ˡ p≼v ∷ ps≼vs) = inj₁ (p≼v ∷ ps≼vs)
  ∣≼*⁻ (∣≼ʳ q≼v ∷ ps≼vs) = inj₂ (q≼v ∷ ps≼vs)

  -- (p ∣ q ∷ ps) ≼* (v ∷ vs) iff (p ∷ ps) ≼* (v ∷ vs) or (q ∷ ps) ≼* (v ∷ vs)
  ∣≼*⇔ : (p ∷ ps ≼* v ∷ vs ⊎ q ∷ ps ≼* v ∷ vs) ⇔ (p ∣ q ∷ ps ≼* v ∷ vs)
  ∣≼*⇔ = mk⇔ ∣≼*⁺ ∣≼*⁻


module _ {c : Con α} {rs : Pats (argsTy α c)} {ps : Pats αs} {us : Vals (argsTy α c)} {vs : Vals αs} where

  con≼*⁺ : (++All⁺ rs ps ≼* ++All⁺ us vs) → con {α} c rs ∷ ps ≼* con c us ∷ vs
  con≼*⁺ rsps≼usvs =
    let rs≼us , ps≼vs = ++⁻ rs rsps≼usvs in
    con≼ rs≼us ∷ ps≼vs

  con≼*⁻ : con {α} c rs ∷ ps ≼* con c us ∷ vs → ++All⁺ rs ps ≼* ++All⁺ us vs
  con≼*⁻ (con≼ rs≼us ∷ ps≼vs) = ++⁺ rs≼us ps≼vs

  -- (con c rs ∷ ps) ≼* (con c us ∷ vs) iff (rs ++ ps) ≼* (us ++ vs)
  con≼*⇔ : (++All⁺ rs ps ≼* ++All⁺ us vs) ⇔ (con {α} c rs ∷ ps ≼* con c us ∷ vs)
  con≼*⇔ = mk⇔ con≼*⁺ con≼*⁻


c≼d→c≡d : {c d : Con α} {ps : Pats (argsTy α c)} {vs : Vals (argsTy α d)}
  → con {α} c ps ≼ con d vs
  → c ≡ d
c≼d→c≡d (con≼ _) = refl

--------------------------------------------------------------------------------
-- Pattern matching

_≼?_ : (p : Pat α) (v : Val α) → Dec (p ≼ v)
_≼*?_ : (ps : Pats αs) (vs : Vals αs) → Dec (ps ≼* vs)

∙ ≼? v = yes ∙≼
con c ps ≼? con d vs with c ≟Fin d
... | yes refl = mapDec con≼⇔ (ps ≼*? vs)
... | no c≢d = no (contraposition c≼d→c≡d c≢d)
p ∣ q ≼? v = mapDec ∣≼⇔ (p ≼? v ⊎-dec q ≼? v)

[] ≼*? [] = yes []
p ∷ ps ≼*? v ∷ vs = mapDec ∷⇔ (p ≼? v ×-dec ps ≼*? vs)

-- First match
Match : PatMat αs → Vals αs → Set
Match P vs = First (_⋠* vs) (_≼* vs) P

match? : (P : PatMat αs) (vs : Vals αs) → Dec (Match P vs)
match? P vs = first? (_≼*? vs) P
