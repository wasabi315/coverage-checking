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

data Instance : (@0 p : Pattern α0) (@0 v : Value α0) → Type
Instances : (@0 ps : Patterns αs0) (@0 vs : Values αs0) → Type

syntax Instance  p  v  = p ≼ v
syntax Instances ps vs = ps ≼* vs

-- p ≼ v : pattern p matches value v
data Instance where
  IWild : {@0 v : Value α0} → — ≼ v

  ICon : {c : NameCon d0}
    → (let @0 αs : Tys
           αs = argsTy (dataDefs sig d0) c)
    → {@0 ps : Patterns αs} {@0 vs : Values αs}
    → (insts : ps ≼* vs)
    → con c ps ≼ con c vs

  IOrL : {@0 p q : Pattern α0} {@0 v : Value α0}
    → (inst : p ≼ v)
    → (p ∣ q) ≼ v

  IOrR : {@0 p q : Pattern α0} {@0 v : Value α0}
    → (inst : q ≼ v)
    → (p ∣ q) ≼ v

pattern —≼         = IWild
pattern con≼ insts = ICon insts
pattern ∣≼ˡ inst   = IOrL inst
pattern ∣≼ʳ inst   = IOrR inst

-- ps ≼* vs : each pattern in ps matches the corresponding value in vs
Instances = HPointwise (λ p v → p ≼ v)

{-# COMPILE AGDA2HS Instance deriving Show #-}
{-# COMPILE AGDA2HS Instances #-}

-- pmat ≼ᵐ vs : some row (clause) in pmat matches vs
InstanceMatrix : (@0 pmat : PatternMatrix αs0) (@0 vs : Values αs0) → Type
syntax InstanceMatrix pmat vs = pmat ≼ᵐ vs
pmat ≼ᵐ vs = Any (λ ps → ps ≼* vs) pmat
{-# COMPILE AGDA2HS InstanceMatrix #-}

_⋠_ : (@0 p : Pattern α0) (@0 v : Value α0) → Type
p ⋠ v = ¬ p ≼ v

_⋠*_ : (@0 ps : Patterns αs0) (@0 vs : Values αs0) → Type
ps ⋠* vs = ¬ ps ≼* vs

_⋠ᵐ_ : (@0 pmat : PatternMatrix αs0) (@0 vs : Values αs0) → Type
pmat ⋠ᵐ vs = ¬ pmat ≼ᵐ vs

--------------------------------------------------------------------------------
-- Properties of the instance relation

-- List of wildcards matches any list of values
iWilds : {@0 vs : Values αs} → —* ≼* vs
iWilds {[]}     {[]}     = []
iWilds {α ∷ αs} {v ∷ vs} = —≼ ∷ iWilds
syntax iWilds = —*≼
{-# COMPILE AGDA2HS iWilds #-}

module _ {@0 p q : Pattern α0} {@0 v : Value α0} where

  -- Inversion lemma for ∣≼ˡ and ∣≼ʳ
  iOrInv : (p ∣ q ≼ v) → Either (p ≼ v) (q ≼ v)
  iOrInv (∣≼ˡ inst) = Left inst
  iOrInv (∣≼ʳ inst) = Right inst
  syntax iOrInv = ∣≼⁻
  {-# COMPILE AGDA2HS iOrInv #-}


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps : Patterns αs} {@0 vs : Values αs}
  where

  -- Inversion lemma for con≼
  iConInv : (con c ps ≼ con c vs) → ps ≼* vs
  iConInv (con≼ insts) = insts
  syntax iConInv = con≼⁻
  {-# COMPILE AGDA2HS iConInv #-}


module _ {@0 p : Pattern α0} {@0 v : Value α0} {@0 ps : Patterns αs0} {@0 vs : Values αs0} where

  -- Inversion lemma for ∷
  iUncons : (p ∷ ps ≼* v ∷ vs) → (p ≼ v) × (ps ≼* vs)
  iUncons (inst ∷ insts) = inst , insts
  syntax iUncons = ∷ⁱ⁻
  {-# COMPILE AGDA2HS iUncons #-}


module _ {c c' : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c
       @0 αs' : Tys
       αs' = argsTy (dataDefs sig d0) c')
  {@0 ps : Patterns αs} {@0 vs : Values αs'}
  where

  -- Constructor names are equal if the constructor pattern matches the corresponding value
  c≼c'⇒c≡c' : con c ps ≼ con c' vs → c ≡ c'
  c≼c'⇒c≡c' (con≼ _) = refl


-- only v matches v
only≼  : (v : Value α0) → only v ≼ v
onlys≼ : (vs : Values αs0) → onlys vs ≼* vs

only≼ (con c vs) = con≼ (onlys≼ vs)

onlys≼ []       = []
onlys≼ (v ∷ vs) = only≼ v ∷ onlys≼ vs

-- only v matches v' implies v ≡ v'
-- Together with only≼, only v ≼ v' is equivalent to v ≡ v'
only≼⇒≡  : {v v' : Value α0} → only v ≼ v' → v ≡ v'
onlys≼⇒≡ : {vs vs' : Values αs0} → onlys vs ≼* vs' → vs ≡ vs'

only≼⇒≡ {v = con c vs} {con c vs'} (con≼ insts) = cong (con c) (onlys≼⇒≡ insts)

onlys≼⇒≡ {vs = []} {[]} [] = refl
onlys≼⇒≡ {vs = v ∷ vs} {v' ∷ vs'} (inst ∷ insts) =
  cong₂ _∷_ (only≼⇒≡ inst) (onlys≼⇒≡ insts)

module _ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  -- p matches exampleFor p
  exampleFor≼  : (p : Pattern α0) → p ≼ exampleFor p
  examplesFor≼ : (ps : Patterns αs0) → ps ≼* examplesFor ps

  exampleFor≼ —          = —≼
  exampleFor≼ (con c ps) = con≼ (examplesFor≼ ps)
  exampleFor≼ (p ∣ _)    = ∣≼ˡ (exampleFor≼ p)

  examplesFor≼ []       = []
  examplesFor≼ (p ∷ ps) = exampleFor≼ p ∷ examplesFor≼ ps

--------------------------------------------------------------------------------
-- Pattern matching
-- Formalized as a decision procedure for the instance relation

decInstance  : (p : Pattern α0) (v : Value α0) → DecP (p ≼ v)
decInstances : (ps : Patterns αs0) (vs : Values αs0) → DecP (ps ≼* vs)

syntax decInstance  p  v  = p ≼? v
syntax decInstances ps vs = ps ≼*? vs

— ≼? v = Yes —≼
(p ∣ q) ≼? v = mapDecP (either ∣≼ˡ ∣≼ʳ) ∣≼⁻ (eitherDecP (p ≼? v) (q ≼? v))
con c ps ≼? con c' vs =
  ifDec (c ≟ c')
    (λ where ⦃ refl ⦄ → mapDecP con≼ con≼⁻ (ps ≼*? vs))
    (λ ⦃ c≢c' ⦄ → No (contraposition c≼c'⇒c≡c' c≢c'))

[] ≼*? [] = Yes []
(p ∷ ps) ≼*? (v ∷ vs) = mapDecP (uncurry _∷_ ) ∷ⁱ⁻ (p ≼? v ×-decP ps ≼*? vs)

{-# COMPILE AGDA2HS decInstance #-}
{-# COMPILE AGDA2HS decInstances #-}

-- First-semantics
FirstMatch : (@0 pmat : PatternMatrix αs0) (@0 vs : Values αs0) → Type
FirstMatch pmat vs = First (λ ps → ps ≼* vs) pmat
{-# COMPILE AGDA2HS FirstMatch #-}

-- Execute pattern matching
decFirstMatch : (pmat : PatternMatrix αs0) (vs : Values αs0)
  → DecP (FirstMatch pmat vs)
decFirstMatch pmat vs = firstDecP (λ ps → ps ≼*? vs) pmat
{-# COMPILE AGDA2HS decFirstMatch #-}
