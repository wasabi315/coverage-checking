open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax

module CoverageCheck.Instance
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

infix 4 Instance Instances InstanceMatrix _⋠_ _⋠*_ _⋠**_
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

data Instance : (@0 p : Pattern α0) (@0 v : Value α0)    → Type
Instances : (@0 ps : Patterns αs0) (@0 vs : Values αs0) → Type

syntax Instance  p v   = p ≼ v
syntax Instances ps vs = ps ≼* vs

-- p ≼ v : pattern p matches value v
data Instance where
  IWild : {@0 v : Value α0} → — ≼ v

  ICon : {c : NameCon d0}
    (let @0 αs : Tys
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
Instances = HPointwise (λ p v → p ≼ v)

{-# COMPILE AGDA2HS Instances #-}

-- P ≼** vs : some row in P matches vs
InstanceMatrix : (@0 P : PatternMatrix αs0) (@0 vs : Values αs0) → Type
syntax InstanceMatrix P vs = P ≼** vs
P ≼** vs = Any (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS InstanceMatrix #-}

_⋠_ : (@0 p : Pattern α0) (@0 v : Value α0) → Type
p ⋠ v = ¬ p ≼ v

_⋠*_ : (@0 ps : Patterns αs0) (@0 vs : Values αs0) → Type
ps ⋠* vs = ¬ ps ≼* vs

_⋠**_ : (@0 P : PatternMatrix αs0) (@0 vs : Values αs0) → Type
P ⋠** vs = ¬ P ≼** vs

--------------------------------------------------------------------------------
-- Properties of the instance relation

iWilds : {@0 vs : Values αs} → —* ≼* vs
iWilds {[]}     {[]}     = []
iWilds {α ∷ αs} {v ∷ vs} = —≼ ∷ iWilds
{-# COMPILE AGDA2HS iWilds #-}
syntax iWilds = —≼*

module _ {@0 p q : Pattern α0} {@0 v : Value α0} where

  iOrInv : (p ∣ q ≼ v) → Either (p ≼ v) (q ≼ v)
  iOrInv (∣≼ˡ h) = Left h
  iOrInv (∣≼ʳ h) = Right h
  {-# COMPILE AGDA2HS iOrInv #-}
  syntax iOrInv = ∣≼⁻


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps : Patterns αs}
  {@0 vs : Values αs}
  where

  iConInv : (con c ps ≼ con c vs) → ps ≼* vs
  iConInv (con≼ is) = is
  {-# COMPILE AGDA2HS iConInv #-}
  syntax iConInv = con≼⁻


module _ {@0 p : Pattern α0} {@0 v : Value α0} {@0 ps : Patterns αs0} {@0 vs : Values αs0} where

  iUncons : (p ∷ ps ≼* v ∷ vs) → (p ≼ v) × (ps ≼* vs)
  iUncons (i ∷ is) = i , is
  {-# COMPILE AGDA2HS iUncons #-}
  syntax iUncons = ∷ⁱ⁻


module _ {c c' : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c
       @0 αs' : Tys
       αs' = argsTy (dataDefs sig d0) c')
  {@0 ps : Patterns αs} {@0 vs : Values αs'}
  where

  c≼c'⇒c≡c' : con c ps ≼ con c' vs → c ≡ c'
  c≼c'⇒c≡c' (con≼ h) = refl


only≼  : (v : Value α0) → only v ≼ v
onlys≼ : (vs : Values αs0) → onlys vs ≼* vs

only≼ (con c vs) = con≼ (onlys≼ vs)

onlys≼ []       = []
onlys≼ (v ∷ vs) = only≼ v ∷ onlys≼ vs

only≼⇒≡  : {v v' : Value α0} → only v ≼ v' → v ≡ v'
onlys≼⇒≡ : {vs vs' : Values αs0} → onlys vs ≼* vs' → vs ≡ vs'

only≼⇒≡ {v = con c vs} {con c vs'} (con≼ is) = cong (con c) (onlys≼⇒≡ is)

onlys≼⇒≡ {vs = []}     {[]}       []       = refl
onlys≼⇒≡ {vs = v ∷ vs} {v' ∷ vs'} (i ∷ is) = cong₂ _∷_  (only≼⇒≡ i) (onlys≼⇒≡ is)

module _ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  exampleFor≼  : (p : Pattern α0) → p ≼ exampleFor p
  examplesFor≼ : (ps : Patterns αs0) → ps ≼* examplesFor ps

  exampleFor≼ —          = —≼
  exampleFor≼ (con c ps) = con≼ (examplesFor≼ ps)
  exampleFor≼ (p ∣ _)    = ∣≼ˡ (exampleFor≼ p)

  examplesFor≼ []       = []
  examplesFor≼ (p ∷ ps) = exampleFor≼ p ∷ examplesFor≼ ps

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

[]       ≼*? []       = Yes []
(p ∷ ps) ≼*? (v ∷ vs) = mapDecP (uncurry _∷_ ) ∷ⁱ⁻ (p ≼? v ×-decP ps ≼*? vs)

{-# COMPILE AGDA2HS decInstance   #-}
{-# COMPILE AGDA2HS decInstances  #-}

Match : (@0 P : PatternMatrix αs0) (@0 vs : Values αs0) → Type
Match P vs = First (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS Match #-}

decMatch : (P : PatternMatrix αs0) (vs : Values αs0) → DecP (Match P vs)
decMatch p vs = firstDecP (λ ps → ps ≼*? vs) p
{-# COMPILE AGDA2HS decMatch #-}
