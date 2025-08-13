open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax

module CoverageCheck.Instance
  {{@0 globals : Globals}}
  {{@0 sig : Signature}}
  where

private open module @0 G = Globals globals

infixr 5 _◂_ _◂◂ⁱ_
infix  4 _≼_ _≼*_ _≼**_ _⋠_ _⋠*_ _⋠**_
         decInstance decInstances

private
  variable
    α β : Type
    αs βs : Types
    @0 α0 β0 : Type
    @0 αs0 βs0 : Types

--------------------------------------------------------------------------------
-- Instance relation

data @0 _≼_  : (p : Pattern α) (v : Value α) → Set
data @0 _≼*_ : (ps : Patterns αs) (vs : Values αs) → Set

-- p ≼ v : pattern p matches value v
data _≼_ where
  —≼ : {v : Value α} → — ≼ v

  con≼ : {d : NameData} {c : NameCon d}
    (let @0 αs : Types
         αs = argsTy (dataDefs sig d) c)
    {ps : Patterns αs}
    {vs : Values αs}
    → (is : ps ≼* vs)
    → con c ps ≼ con c vs

  ∣≼ˡ : {p q : Pattern α} {v : Value α}
    → (i : p ≼ v)
    → (p ∣ q) ≼ v

  ∣≼ʳ : {p q : Pattern α} {v : Value α}
    → (i : q ≼ v)
    → (p ∣ q) ≼ v

-- ps ≼* vs : each pattern in ps matches the corresponding value in vs
data _≼*_ where
  INil  : ⌈⌉ ≼* ⌈⌉
  ICons : {p : Pattern α} {v : Value α} {ps : Patterns αs} {vs : Values αs}
    → (i : p ≼ v)
    → (is : ps ≼* vs)
    → (p ◂ ps) ≼* (v ◂ vs)

pattern ⌈⌉       = INil
pattern _◂_ i is = ICons i is

-- P ≼** vs : some row in P matches vs
@0 _≼**_ : (P : PatternMatrix αs) (vs : Values αs) → Set
P ≼** vs = Any (_≼* vs) P

@0 _⋠_ : (p : Pattern α) (v : Value α) → Set
p ⋠ v = ¬ p ≼ v

@0 _⋠*_ : (ps : Patterns αs) (vs : Values αs) → Set
ps ⋠* vs = ¬ ps ≼* vs

@0 _⋠**_ : (P : PatternMatrix αs) (vs : Values αs) → Set
P ⋠** vs = ¬ P ≼** vs

--------------------------------------------------------------------------------
-- Properties of the instance relation

@0 —≼* : {vs : Values αs} → —* ≼* vs
—≼* {⌈⌉}     {⌈⌉}     = ⌈⌉
—≼* {α ◂ αs} {v ◂ vs} = —≼ ◂ —≼*

module @0 _ {p q : Pattern α} {v : Value α} where

  ∣≼⁻ : (p ∣ q ≼ v) → Either (p ≼ v) (q ≼ v)
  ∣≼⁻ (∣≼ˡ h) = Left h
  ∣≼⁻ (∣≼ʳ h) = Right h


module @0 _ {d : NameData} {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {ps : Patterns αs}
  {vs : Values αs}
  where

  con≼⁻ : (con c ps ≼ con c vs) → ps ≼* vs
  con≼⁻ (con≼ is) = is


module @0 _ {p : Pattern α} {v : Value α} {ps : Patterns αs} {vs : Values αs} where

  ◂ⁱ⁻ : (p ◂ ps ≼* v ◂ vs) → (p ≼ v) × (ps ≼* vs)
  ◂ⁱ⁻ (i ◂ is) = i , is


-- append instances
@0 _◂◂ⁱ_ : {ps : Patterns αs} {us : Values αs} {qs : Patterns βs} {vs : Values βs}
  → ps ≼* us
  → qs ≼* vs
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
⌈⌉         ◂◂ⁱ is2 = is2
(i1 ◂ is1) ◂◂ⁱ is2 = i1 ◂ (is1 ◂◂ⁱ is2)

@0 ◂◂ⁱ⁻ : (ps : Patterns αs) {us : Values αs} {qs : Patterns βs} {vs : Values βs}
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
  → (ps ≼* us) × (qs ≼* vs)
◂◂ⁱ⁻ ⌈⌉       {⌈⌉}    is       = ⌈⌉ , is
◂◂ⁱ⁻ (p ◂ ps) {_ ◂ _} (i ◂ is) = first (i ◂_) (◂◂ⁱ⁻ ps is)

@0 splitInstances : ∀ (ps : Patterns αs) {qs : Patterns βs} {us : Values (αs ◂◂ βs)}
  → (ps ◂◂ᵖ qs) ≼* us
  → Σ[ vs ∈ _ ] Σ[ ws ∈ _ ] (vs ◂◂ᵛ ws) ≡ us × (ps ≼* vs × qs ≼* ws)
splitInstances ⌈⌉       {us = us}     is       = _ , (_ , (refl , (⌈⌉ , is)))
splitInstances (p ◂ ps) {us = u ◂ us} (i ◂ is) =
  let _ , (_ , (eq , is')) = splitInstances ps is in
  _ , (_ , (cong (u ◂_) eq , first (i ◂_) is'))

-- -- βs is not erasable
-- module _ {@0 αs} {βs} {@0 ps : Patterns αs} {@0 u : Value β} {@0 us : Values βs} {@0 vs} where

--   wildHeadLemma : (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (— ◂ ps) ≼* (u ◂ vs)
--   wildHeadLemma h =
--     let _ , h' = unappendInstances —* h in
--     —≼ ◂ h'
--   {-# COMPILE AGDA2HS wildHeadLemma #-}

--   wildHeadLemmaInv : (— ◂ ps) ≼* (u ◂ vs) → (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
--   wildHeadLemmaInv (—≼ ◂ h) = —≼* ◂◂ⁱ h
--   {-# COMPILE AGDA2HS wildHeadLemmaInv #-}


-- module _ {@0 p q : Pattern α} {@0 ps : Patterns αs} {@0 v} {@0 vs} where

--   orHeadLemma : Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs) → (p ∣ q ◂ ps) ≼* (v ◂ vs)
--   orHeadLemma (Left (h ◂ hs))  = ∣≼ˡ h ◂ hs
--   orHeadLemma (Right (h ◂ hs)) = ∣≼ʳ h ◂ hs
--   {-# COMPILE AGDA2HS orHeadLemma #-}

--   orHeadLemmaInv : (p ∣ q ◂ ps) ≼* (v ◂ vs) → Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
--   orHeadLemmaInv (∣≼ˡ h ◂ hs) = Left (h ◂ hs)
--   orHeadLemmaInv (∣≼ʳ h ◂ hs) = Right (h ◂ hs)
--   {-# COMPILE AGDA2HS orHeadLemmaInv #-}


-- -- rs is not erasable
-- module _ {@0 d : NameData} {c : NameCon d}
--   (let @0 αs : Types
--        αs = argsTy (dataDefs sig d) c)
--   {rs : Patterns αs}
--   {@0 ps : Patterns βs}
--   {@0 us : Values αs}
--   {@0 vs : Values βs}
--   where

--   conHeadLemma : (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (con c rs ◂ ps) ≼* (con c us ◂ vs)
--   conHeadLemma h =
--     let h1 , h2 = unappendInstances rs h in
--     con≼ h1 ◂ h2
--   {-# COMPILE AGDA2HS conHeadLemma #-}

--   conHeadLemmaInv : (con c rs ◂ ps) ≼* (con c us ◂ vs) → (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
--   conHeadLemmaInv (con≼ h ◂ h') = h ◂◂ⁱ h'
--   {-# COMPILE AGDA2HS conHeadLemmaInv #-}


module _ {d : NameData} {c c' : NameCon d}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d) c
       @0 αs' : Types
       αs' = argsTy (dataDefs sig d) c')
  {ps : Patterns αs}
  {vs : Values αs'}
  where

  c≼c'⇒c≡c' : con c ps ≼ con c' vs → c ≡ c'
  c≼c'⇒c≡c' (con≼ h) = refl

--------------------------------------------------------------------------------
-- Pattern matching

decInstance  : (p : Pattern α0) (v : Value α0) → Dec (p ≼ v)
decInstances : (ps : Patterns αs0) (vs : Values αs0) → Dec (ps ≼* vs)

syntax decInstance  p  v  = p ≼? v
syntax decInstances ps vs = ps ≼*? vs

con c ps ≼? con c' vs = ifDec (c ≟ c')
  (λ where {{refl}} → mapDec con≼ con≼⁻ (ps ≼*? vs))
  (λ {{h}} → False ⟨ contraposition c≼c'⇒c≡c' h ⟩)
—       ≼? v = True ⟨ —≼ ⟩
(p ∣ q) ≼? v = mapDec (either ∣≼ˡ ∣≼ʳ) ∣≼⁻ (eitherDec (p ≼? v) (q ≼? v))

⌈⌉       ≼*? ⌈⌉       = True ⟨ ⌈⌉ ⟩
(p ◂ ps) ≼*? (v ◂ vs) = mapDec (uncurry _◂_) ◂ⁱ⁻ (p ≼? v ×-dec ps ≼*? vs)

{-# COMPILE AGDA2HS decInstance   #-}
{-# COMPILE AGDA2HS decInstances  #-}

@0 Match : (P : PatternMatrix αs) (vs : Values αs) → Set
Match P vs = First (_⋠* vs) (_≼* vs) P

decMatch : (P : PatternMatrix αs0) (vs : Values αs0) → Dec (Match P vs)
decMatch p vs = firstDec (λ ps → ps ≼*? vs) p
{-# COMPILE AGDA2HS decMatch #-}
