open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax

module CoverageCheck.Instance
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

infix 4 Instance Instances InstanceMatrix _⋠_ _⋠*_ _⋠ᵐ_
        decInstance decInstances

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Instance relation

data Instance : (@0 v : Value α0) (@0 p : Pattern α0) → Type
Instances : (@0 vs : Values αs0) (@0 ps : Patterns αs0) → Type

syntax Instance  v  p  = v ≼ p
syntax Instances vs ps = vs ≼* ps

-- v ≼ p : value v matches pattern p (or value v is an instance of pattern p)
data Instance where
  IWild : {@0 v : Value α0} → v ≼ —

  ICon : {c : NameCon d0}
    → (let @0 αs : Tys
           αs = argsTy (dataDefs sig d0) c)
    → {@0 vs : Values αs} {@0 ps : Patterns αs}
    → (insts : vs ≼* ps)
    → con c vs ≼ con c ps

  IOrL : {@0 v : Value α0} {@0 p q : Pattern α0}
    → (inst : v ≼ p)
    → v ≼ (p ∣ q)

  IOrR : {@0 v : Value α0} {@0 p q : Pattern α0}
    → (inst : v ≼ q)
    → v ≼ (p ∣ q)

pattern —≼         = IWild
pattern con≼ insts = ICon insts
pattern ∣≼ˡ inst   = IOrL inst
pattern ∣≼ʳ inst   = IOrR inst

-- vs ≼* ps : each value in vs matches the corresponding pattern in ps
Instances = HPointwise (λ v p → v ≼ p)

{-# COMPILE AGDA2HS Instance deriving Show #-}
{-# COMPILE AGDA2HS Instances #-}

-- vs ≼ᵐ pmat : some row (clause) in pmat matches vs
InstanceMatrix : (@0 vs : Values αs0) (@0 pmat : PatternMatrix αs0) → Type
syntax InstanceMatrix vs pmat = vs ≼ᵐ pmat
vs ≼ᵐ pmat = Any (λ ps → vs ≼* ps) pmat
{-# COMPILE AGDA2HS InstanceMatrix #-}

_⋠_ : (@0 v : Value α0) (@0 p : Pattern α0) → Type
v ⋠ p = ¬ v ≼ p

_⋠*_ : (@0 vs : Values αs0) (@0 ps : Patterns αs0) → Type
vs ⋠* ps = ¬ vs ≼* ps

_⋠ᵐ_ : (@0 vs : Values αs0) (@0 pmat : PatternMatrix αs0) → Type
vs ⋠ᵐ pmat = ¬ vs ≼ᵐ pmat

--------------------------------------------------------------------------------
-- Properties of the instance relation

-- List of wildcards matches any list of values
iWilds : {@0 vs : Values αs} → vs ≼* —*
iWilds {[]}     {[]}     = []
iWilds {α ∷ αs} {v ∷ vs} = —≼ ∷ iWilds
syntax iWilds = —*≼
{-# COMPILE AGDA2HS iWilds #-}

module _ {@0 v : Value α0} {@0 p q : Pattern α0} where

  -- Inversion lemma for ∣≼ˡ and ∣≼ʳ
  iOrInv : (v ≼ p ∣ q) → Either (v ≼ p) (v ≼ q)
  iOrInv (∣≼ˡ inst) = Left inst
  iOrInv (∣≼ʳ inst) = Right inst
  syntax iOrInv = ∣≼⁻
  {-# COMPILE AGDA2HS iOrInv #-}


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 vs : Values αs} {@0 ps : Patterns αs}
  where

  -- Inversion lemma for con≼
  iConInv : (con c vs ≼ con c ps) → vs ≼* ps
  iConInv (con≼ insts) = insts
  syntax iConInv = con≼⁻
  {-# COMPILE AGDA2HS iConInv #-}


module _
  {@0 v : Value α0} {@0 p : Pattern α0}
  {@0 vs : Values αs0} {@0 ps : Patterns αs0}
  where

  -- Inversion lemma for ∷
  iUncons : (v ∷ vs ≼* p ∷ ps) → (v ≼ p) × (vs ≼* ps)
  iUncons (inst ∷ insts) = inst , insts
  syntax iUncons = ∷ⁱ⁻
  {-# COMPILE AGDA2HS iUncons #-}


module _ {c c' : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c
       @0 αs' : Tys
       αs' = argsTy (dataDefs sig d0) c')
  {@0 vs : Values αs'} {@0 ps : Patterns αs}
  where

  -- Constructor names are equal if the constructor pattern matches the corresponding value
  c≼c'⇒c≡c' : con c' vs ≼ con c ps → c ≡ c'
  c≼c'⇒c≡c' (con≼ _) = refl


-- only v matches v
only≼  : (v : Value α0) → v ≼ only v
onlys≼ : (vs : Values αs0) → vs ≼* onlys vs

only≼ (con c vs) = con≼ (onlys≼ vs)

onlys≼ [] = []
onlys≼ (v ∷ vs) = only≼ v ∷ onlys≼ vs

-- only v matches v' implies v ≡ v'
-- Together with only≼, v ≼ only v' is equivalent to v ≡ v'
only≼⇒≡  : {v v' : Value α0} → v ≼ only v' → v ≡ v'
onlys≼⇒≡ : {vs vs' : Values αs0} → vs ≼* onlys vs' → vs ≡ vs'

only≼⇒≡ {v = con c vs} {con c vs'} (con≼ insts) = cong (con c) (onlys≼⇒≡ insts)

onlys≼⇒≡ {vs = []} {[]} [] = refl
onlys≼⇒≡ {vs = v ∷ vs} {v' ∷ vs'} (inst ∷ insts) =
  cong₂ _∷_ (only≼⇒≡ inst) (onlys≼⇒≡ insts)

module _ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  -- p matches exampleFor p
  exampleFor≼  : (p : Pattern α0) → exampleFor p ≼ p
  examplesFor≼ : (ps : Patterns αs0) → examplesFor ps ≼* ps

  exampleFor≼ —          = —≼
  exampleFor≼ (con c ps) = con≼ (examplesFor≼ ps)
  exampleFor≼ (p ∣ _)    = ∣≼ˡ (exampleFor≼ p)

  examplesFor≼ []       = []
  examplesFor≼ (p ∷ ps) = exampleFor≼ p ∷ examplesFor≼ ps

--------------------------------------------------------------------------------
-- Pattern matching
-- Formalized as a decision procedure for the instance relation

decInstance  : (v : Value α0) (p : Pattern α0) → DecP (v ≼ p)
decInstances : (vs : Values αs0) (ps : Patterns αs0) → DecP (vs ≼* ps)

syntax decInstance  v  p  = v ≼? p
syntax decInstances vs ps = vs ≼*? ps

v ≼? — = Yes —≼
v ≼? (p ∣ q) = mapDecP (either ∣≼ˡ ∣≼ʳ) ∣≼⁻ (eitherDecP (v ≼? p) (v ≼? q))
con c vs ≼? con c' ps =
  ifDec (c ≟ c')
    (λ where ⦃ refl ⦄ → mapDecP con≼ con≼⁻ (vs ≼*? ps))
    (λ ⦃ c≢c' ⦄ → No (contraposition c≼c'⇒c≡c' (c≢c' ∘ sym)))

[] ≼*? [] = Yes []
(v ∷ vs) ≼*? (p ∷ ps) = mapDecP (uncurry _∷_ ) ∷ⁱ⁻ (v ≼? p ×-decP vs ≼*? ps)

{-# COMPILE AGDA2HS decInstance #-}
{-# COMPILE AGDA2HS decInstances #-}

-- First-match semantics
FirstMatch : (@0 vs : Values αs0) (@0 pmat : PatternMatrix αs0) → Type
FirstMatch vs pmat = First (λ ps → vs ≼* ps) pmat
{-# COMPILE AGDA2HS FirstMatch #-}

-- Execute pattern matching
decPFirstMatch : (vs : Values αs0) (pmat : PatternMatrix αs0)
  → DecP (FirstMatch vs pmat)
decPFirstMatch vs pmat = firstDecP (λ ps → vs ≼*? ps) pmat
{-# COMPILE AGDA2HS decPFirstMatch #-}
