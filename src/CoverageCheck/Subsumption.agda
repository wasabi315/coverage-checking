open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Instance

module CoverageCheck.Subsumption
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

infix 4 Subsumption Subsumptions _⊈_ _⊈*_

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Subsumption

data Subsumption : (@0 p q : Pattern α0) → Type
Subsumptions : (@0 ps qs : Patterns αs0) → Type

syntax Subsumption  p  q  = p ⊆ q
syntax Subsumptions ps qs = ps ⊆* qs

-- p ⊆ q : p subsumes q
-- Not complete; for example, (true ∣ false) ⊆ — is not derivable
-- Probably better named BranchSelection
data Subsumption where
  SWild : {@0 q : Pattern α0} → — ⊆ q

  SCon : {c : NameCon d0}
    → (let @0 αs : Tys
           αs = argsTy (dataDefs sig d0) c)
    → {@0 ps qs : Patterns αs}
    → (subs : ps ⊆* qs)
    → con c ps ⊆ con c qs

  SOrL : {@0 p q r : Pattern α0}
    → (sub : p ⊆ r)
    → (p ∣ q) ⊆ r

  SOrR : {@0 p q r : Pattern α0}
    → (sub : q ⊆ r)
    → (p ∣ q) ⊆ r

{-# COMPILE AGDA2HS Subsumption deriving Show #-}

pattern —⊆        = SWild
pattern con⊆ subs = SCon subs
pattern ∣⊆ˡ sub   = SOrL sub
pattern ∣⊆ʳ sub   = SOrR sub

Subsumptions = HPointwise (λ p q → p ⊆ q)

{-# COMPILE AGDA2HS Subsumptions #-}

_⊈_ : (@0 p q : Pattern α0) → Type
p ⊈ q = ¬ p ⊆ q

_⊈*_ : (@0 ps qs : Patterns αs0) → Type
qs ⊈* ps = ¬ ps ⊆* qs

--------------------------------------------------------------------------------
-- Properties of the subsumption relation

-- List of wildcards subsumes any list of patterns
sWilds : {@0 qs : Patterns αs} → Subsumptions {αs} —* qs
sWilds {[]}     {[]}    = []
sWilds {α ∷ αs} {_ ∷ _} = —⊆ ∷ sWilds
{-# COMPILE AGDA2HS sWilds #-}
syntax sWilds = —⊆*

module _ {@0 p q r : Pattern α0} where

  -- Inversion lemma for ∣⊆ˡ and ∣⊆ʳ
  sOrInv : (p ∣ q ⊆ r) → Either (p ⊆ r) (q ⊆ r)
  sOrInv (∣⊆ˡ sub) = Left sub
  sOrInv (∣⊆ʳ sub) = Right sub
  {-# COMPILE AGDA2HS sOrInv #-}
  syntax sOrInv = ∣⊆⁻


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps qs : Patterns αs}
  where

  -- Inversion lemma for con⊆
  sConInv : (con c ps ⊆ con c qs) → ps ⊆* qs
  sConInv (con⊆ subs) = subs
  {-# COMPILE AGDA2HS sConInv #-}
  syntax sConInv = con⊆⁻

-- ⊆ implies the "semantic" version of subsumption relation
subsume : {p q : Pattern α0} {v : Value α0}
  → p ⊆ q
  → (q ≼ v → p ≼ v)
subsumes : {ps qs : Patterns αs0} {vs : Values αs0}
  → ps ⊆* qs
  → (qs ≼* vs → ps ≼* vs)

subsume —⊆ inst = —≼
subsume (con⊆ subs) (con≼ insts) = con≼ (subsumes subs insts)
subsume (∣⊆ˡ sub) inst = ∣≼ˡ (subsume sub inst)
subsume (∣⊆ʳ sub) inst = ∣≼ʳ (subsume sub inst)

subsumes [] [] = []
subsumes (sub ∷ subs) (inst ∷ insts) = subsume sub inst ∷ subsumes subs insts

⊆only : {p : Pattern α0} {v : Value α0}
  → p ≼ v
  → p ⊆ only v
⊆onlys : {ps : Patterns αs0} {vs : Values αs0}
  → ps ≼* vs
  → ps ⊆* onlys vs

⊆only —≼ = —⊆
⊆only (con≼ insts) = con⊆ (⊆onlys insts)
⊆only (∣≼ˡ inst) = ∣⊆ˡ (⊆only inst)
⊆only (∣≼ʳ inst) = ∣⊆ʳ (⊆only inst)

⊆onlys [] = []
⊆onlys (inst ∷ insts) = ⊆only inst ∷ ⊆onlys insts
