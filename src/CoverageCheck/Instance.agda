open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax

module CoverageCheck.Instance
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

infixr 5 _◂_ appendInstances
infix  4 Instance Instances InstanceMatrix _⋠_ _⋠*_ _⋠**_
         decInstance decInstances

private
  variable
    α β : Type
    αs βs : Types
    d : NameData
    @0 α0 β0 : Type
    @0 αs0 βs0 : Types
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Instance relation

data Instance  : (@0 p : Pattern α0)    (@0 v : Value α0)    → Set
data Instances : (@0 ps : Patterns αs0) (@0 vs : Values αs0) → Set

syntax Instance  p v   = p ≼ v
syntax Instances ps vs = ps ≼* vs

-- p ≼ v : pattern p matches value v
data Instance where
  IWild : {@0 v : Value α0} → — ≼ v

  ICon : {c : NameCon d0}
    (let @0 αs : Types
         αs = argsTy (dataDefs sig d0) c)
    {@0 ps : Patterns αs}
    {@0 vs : Values αs}
    → (is : ps ≼* vs)
    → con c ps ≼ con c vs

  IOrL : {@0 p q : Pattern α0} {@0 v : Value α0}
    → (i : p ≼ v)
    → (p ∣ q) ≼ v

  IOrR : {@0 p q : Pattern α0} {@0 v : Value α0}
    → (i : q ≼ v)
    → (p ∣ q) ≼ v

{-# COMPILE AGDA2HS Instance deriving Show #-}

pattern —≼      = IWild
pattern con≼ is = ICon is
pattern ∣≼ˡ i   = IOrL i
pattern ∣≼ʳ i   = IOrR i

-- ps ≼* vs : each pattern in ps matches the corresponding value in vs
data Instances where
  INil  : ⌈⌉ ≼* ⌈⌉
  ICons : {@0 p : Pattern α0} {@0 v : Value α0} {@0 ps : Patterns αs0} {@0 vs : Values αs0}
    → (i : p ≼ v)
    → (is : ps ≼* vs)
    → (p ◂ ps) ≼* (v ◂ vs)

{-# COMPILE AGDA2HS Instances deriving Show #-}

pattern ⌈⌉       = INil
pattern _◂_ i is = ICons i is

-- P ≼** vs : some row in P matches vs
InstanceMatrix : (@0 P : PatternMatrix αs0) (@0 vs : Values αs0) → Set
syntax InstanceMatrix P vs = P ≼** vs
P ≼** vs = Any (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS InstanceMatrix #-}

@0 _⋠_ : (p : Pattern α0) (v : Value α0) → Set
p ⋠ v = ¬ p ≼ v

@0 _⋠*_ : (ps : Patterns αs0) (vs : Values αs0) → Set
ps ⋠* vs = ¬ ps ≼* vs

@0 _⋠**_ : (P : PatternMatrix αs0) (vs : Values αs0) → Set
P ⋠** vs = ¬ P ≼** vs

--------------------------------------------------------------------------------
-- Properties of the instance relation

iWilds : {@0 vs : Values αs} → —* ≼* vs
iWilds {⌈⌉}     {⌈⌉}     = ⌈⌉
iWilds {α ◂ αs} {v ◂ vs} = —≼ ◂ iWilds
{-# COMPILE AGDA2HS iWilds #-}
syntax iWilds = —≼*

module _ {@0 p q : Pattern α0} {@0 v : Value α0} where

  iOrInv : (p ∣ q ≼ v) → Either (p ≼ v) (q ≼ v)
  iOrInv (∣≼ˡ h) = Left h
  iOrInv (∣≼ʳ h) = Right h
  {-# COMPILE AGDA2HS iOrInv #-}
  syntax iOrInv = ∣≼⁻


module _ {@0 c : NameCon d0}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps : Patterns αs}
  {@0 vs : Values αs}
  where

  iConInv : (con c ps ≼ con c vs) → ps ≼* vs
  iConInv (con≼ is) = is
  {-# COMPILE AGDA2HS iConInv #-}
  syntax iConInv = con≼⁻


module _ {@0 p : Pattern α0} {@0 v : Value α0} {@0 ps : Patterns αs0} {@0 vs : Values αs0} where

  iUncons : (p ◂ ps ≼* v ◂ vs) → (p ≼ v) × (ps ≼* vs)
  iUncons (i ◂ is) = i , is
  {-# COMPILE AGDA2HS iUncons #-}
  syntax iUncons = ◂ⁱ⁻


appendInstances : {@0 ps : Patterns αs0} {@0 us : Values αs0} {@0 qs : Patterns βs0} {@0 vs : Values βs0}
  → ps ≼* us
  → qs ≼* vs
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
appendInstances ⌈⌉         is2 = is2
appendInstances (i1 ◂ is1) is2 = i1 ◂ appendInstances is1 is2
{-# COMPILE AGDA2HS appendInstances #-}
syntax appendInstances is1 is2 = is1 ◂◂ⁱ is2

unappendInstances : (ps : Patterns αs0) {@0 us : Values αs0} {@0 qs : Patterns βs0} {@0 vs : Values βs0}
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
  → (ps ≼* us) × (qs ≼* vs)
unappendInstances ⌈⌉       {⌈⌉}    is       = ⌈⌉ , is
unappendInstances (p ◂ ps) {_ ◂ _} (i ◂ is) = first (i ◂_) (unappendInstances ps is)
{-# COMPILE AGDA2HS unappendInstances #-}
syntax unappendInstances = ◂◂ⁱ⁻

splitInstances : (@0 ps : Patterns αs) {@0 qs : Patterns βs0} {us : Values (αs ◂◂ βs0)}
  → @0 (ps ◂◂ᵖ qs) ≼* us
  → ∃[ (vs , ws) ∈ (Values αs × Values βs0) ] (vs ◂◂ᵛ ws ≡ us) × ((ps ≼* vs) × (qs ≼* ws))
splitInstances {αs = ⌈⌉}     ⌈⌉       {us = us}     is       = (⌈⌉ , us) ⟨ refl , (⌈⌉ , is) ⟩
splitInstances {αs = α ◂ αs} (p ◂ ps) {us = u ◂ us} (i ◂ is) =
  case splitInstances ps is of λ where
    ((vs , ws) ⟨ eq , is' ⟩) → (u ◂ vs , ws) ⟨ cong (u ◂_) eq , first (i ◂_) is' ⟩
{-# COMPILE AGDA2HS splitInstances #-}

module _ {@0 ps : Patterns αs0} {@0 vs : Values αs0} {@0 u : Value β0} {@0 us : Values βs} where

  wildHeadLemma : (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (— ◂ ps) ≼* (u ◂ vs)
  wildHeadLemma h = case unappendInstances —* h of λ where
    (_ , h') → —≼ ◂ h'
  {-# COMPILE AGDA2HS wildHeadLemma #-}

  wildHeadLemmaInv : (— ◂ ps) ≼* (u ◂ vs) → (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
  wildHeadLemmaInv (—≼ ◂ h) = —≼* ◂◂ⁱ h
  {-# COMPILE AGDA2HS wildHeadLemmaInv #-}


module _ {@0 p q : Pattern α0} {@0 ps : Patterns αs0} {@0 v : Value α0} {@0 vs : Values αs0} where

  orHeadLemma : Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
    → (p ∣ q ◂ ps) ≼* (v ◂ vs)
  orHeadLemma (Left (h ◂ hs))  = ∣≼ˡ h ◂ hs
  orHeadLemma (Right (h ◂ hs)) = ∣≼ʳ h ◂ hs
  {-# COMPILE AGDA2HS orHeadLemma #-}

  orHeadLemmaInv : (p ∣ q ◂ ps) ≼* (v ◂ vs)
    → Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
  orHeadLemmaInv (∣≼ˡ h ◂ hs) = Left (h ◂ hs)
  orHeadLemmaInv (∣≼ʳ h ◂ hs) = Right (h ◂ hs)
  {-# COMPILE AGDA2HS orHeadLemmaInv #-}


module _ {c : NameCon d0}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d0) c)
  {rs : Patterns αs} {@0 ps : Patterns βs0}
  {@0 us : Values αs} {@0 vs : Values βs0}
  where

  conHeadLemma : (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
    → (con c rs ◂ ps) ≼* (con c us ◂ vs)
  conHeadLemma h = case unappendInstances rs h of λ where
    (h1 , h2) → con≼ h1 ◂ h2
  {-# COMPILE AGDA2HS conHeadLemma #-}


module _ {@0 c : NameCon d0}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d0) c)
  {rs : Patterns αs} {@0 ps : Patterns βs0}
  {@0 us : Values αs} {@0 vs : Values βs0}
  where

  conHeadLemmaInv : (con c rs ◂ ps) ≼* (con c us ◂ vs)
    → (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
  conHeadLemmaInv (con≼ h ◂ h') = h ◂◂ⁱ h'
  {-# COMPILE AGDA2HS conHeadLemmaInv #-}


module _ {c c' : NameCon d0}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d0) c
       @0 αs' : Types
       αs' = argsTy (dataDefs sig d0) c')
  {@0 ps : Patterns αs} {@0 vs : Values αs'}
  where

  c≼c'⇒c≡c' : con c ps ≼ con c' vs → c ≡ c'
  c≼c'⇒c≡c' (con≼ h) = refl

--------------------------------------------------------------------------------
-- Pattern matching

decInstance  : (p : Pattern α0) (v : Value α0) → DecP (p ≼ v)
decInstances : (ps : Patterns αs0) (vs : Values αs0) → DecP (ps ≼* vs)

syntax decInstance  p  v  = p ≼? v
syntax decInstances ps vs = ps ≼*? vs

—        ≼? v         = Yes —≼
(p ∣ q)  ≼? v         = mapDecP (either ∣≼ˡ ∣≼ʳ) ∣≼⁻ (eitherDecP (p ≼? v) (q ≼? v))
con c ps ≼? con c' vs =
  ifDec (c ≟ c')
    (λ where ⦃ refl ⦄ → mapDecP con≼ con≼⁻ (ps ≼*? vs))
    (λ ⦃ h ⦄ → No (contraposition c≼c'⇒c≡c' h))

⌈⌉       ≼*? ⌈⌉       = Yes ⌈⌉
(p ◂ ps) ≼*? (v ◂ vs) = mapDecP (uncurry _◂_) ◂ⁱ⁻ (p ≼? v ×-decP ps ≼*? vs)

{-# COMPILE AGDA2HS decInstance   #-}
{-# COMPILE AGDA2HS decInstances  #-}

Match : (@0 P : PatternMatrix αs0) (@0 vs : Values αs0) → Set
Match P vs = First (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS Match #-}

decMatch : (P : PatternMatrix αs0) (vs : Values αs0) → DecP (Match P vs)
decMatch p vs = firstDecP (λ ps → ps ≼*? vs) p
{-# COMPILE AGDA2HS decMatch #-}
