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

infixr 5 _∷_  appendSubsumptions
infix  4 Subsumption Subsumptions _⊈_ _⊈*_

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

data Subsumption  : (@0 p q : Pattern α0)     → Type
data Subsumptions : (@0 ps qs : Patterns αs0) → Type

syntax Subsumption  p  q  = p ⊆ q
syntax Subsumptions ps qs = ps ⊆* qs

-- p ⊆ q : p is a subsumption of q
data Subsumption where
  SWild : {@0 q : Pattern α0} → — ⊆ q

  SCon : {c : NameCon d0}
    (let @0 αs : Tys
         αs = argsTy (dataDefs sig d0) c)
    {@0 ps qs : Patterns αs}
    → (ss : ps ⊆* qs)
    → con c ps ⊆ con c qs

  SOrL : {@0 p q r : Pattern α0}
    → (s : p ⊆ r)
    → (p ∣ q) ⊆ r

  SOrR : {@0 p q r : Pattern α0}
    → (s : q ⊆ r)
    → (p ∣ q) ⊆ r

{-# COMPILE AGDA2HS Subsumption deriving Show #-}

pattern —⊆      = SWild
pattern con⊆ bs = SCon bs
pattern ∣⊆ˡ s   = SOrL s
pattern ∣⊆ʳ s   = SOrR s

data Subsumptions where
  SNil : [] ⊆* []
  SCons : {@0 p q : Pattern α0} {@0 ps qs : Patterns αs0}
    → (s : p ⊆ q)
    → (ss : ps ⊆* qs)
    → (p ∷ ps) ⊆* (q ∷ qs)

{-# COMPILE AGDA2HS Subsumptions deriving Show #-}

pattern []       = SNil
pattern _∷_  s ss = SCons s ss

_⊈_ : (@0 p q : Pattern α0) → Type
p ⊈ q = ¬ p ⊆ q

_⊈*_ : (@0 ps qs : Patterns αs0) → Type
qs ⊈* ps = ¬ ps ⊆* qs

--------------------------------------------------------------------------------
-- Properties of the branch selection relation

sWilds : {@0 qs : Patterns αs} → Subsumptions {αs} —* qs
sWilds {[]}     {[]}    = []
sWilds {α ∷ αs} {_ ∷ _} = —⊆ ∷ sWilds
{-# COMPILE AGDA2HS sWilds #-}
syntax sWilds = —⊆*

module _ {@0 p q r : Pattern α0} where

  sOrInv : (p ∣ q ⊆ r) → Either (p ⊆ r) (q ⊆ r)
  sOrInv (∣⊆ˡ s) = Left s
  sOrInv (∣⊆ʳ s) = Right s
  {-# COMPILE AGDA2HS sOrInv #-}
  syntax sOrInv = ∣⊆⁻


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps qs : Patterns αs}
  where

  sConInv : (con c ps ⊆ con c qs) → ps ⊆* qs
  sConInv (con⊆ ss) = ss
  {-# COMPILE AGDA2HS sConInv #-}
  syntax sConInv = con⊆⁻


appendSubsumptions : {@0 ps ps' : Patterns αs0} {@0 qs qs' : Patterns βs0}
  → (ps ⊆* ps')
  → (qs ⊆* qs')
  → (ps ++ᵖ qs) ⊆* (ps' ++ᵖ qs')
appendSubsumptions [] bs' = bs'
appendSubsumptions (s ∷ ss) ss' = s ∷ appendSubsumptions ss ss'
{-# COMPILE AGDA2HS appendSubsumptions #-}
syntax appendSubsumptions bs bs' = bs ++ˢ bs'

unappendSubsumptions : (ps : Patterns αs0) {@0 ps' : Patterns αs0} {@0 qs qs' : Patterns βs0}
  → (ps ++ᵖ qs) ⊆* (ps' ++ᵖ qs')
  → (ps ⊆* ps') × (qs ⊆* qs')
unappendSubsumptions []       {[]}    bs       = [] , bs
unappendSubsumptions (p ∷ ps) {_ ∷ _} (s ∷ ss) = first (s ∷_) (unappendSubsumptions ps ss)
{-# COMPILE AGDA2HS unappendSubsumptions #-}
syntax unappendSubsumptions ps bs = ps ++ˢ⁻ bs

splitSubsumptions : (@0 ps : Patterns αs) {@0 qs : Patterns βs0} {rs : Patterns (αs ++ βs0)}
  → @0 (ps ++ᵖ qs) ⊆* rs
  → ∃[ (rs₁ , rs₂) ∈ (Patterns αs × Patterns βs0) ] (rs₁ ++ᵖ rs₂ ≡ rs) × ((ps ⊆* rs₁) × (qs ⊆* rs₂))
splitSubsumptions {αs = []} [] {rs = rs} bs = ([] , rs) ⟨ refl , ([] , bs) ⟩
splitSubsumptions {αs = α ∷ αs} (p ∷ ps) {rs = r ∷ rs} (s ∷ ss) =
  let rs' ⟨ eq , ss' ⟩ = splitSubsumptions ps ss in
  first (r ∷_) rs' ⟨ cong (r ∷_) eq , first (s ∷_) ss' ⟩
{-# COMPILE AGDA2HS splitSubsumptions #-}


subsume : {@0 p q : Pattern α0} {@0 v : Value α0}
  → p ⊆ q
  → q ≼ v
  → p ≼ v
subsumeConCase : {@0 c : NameCon d0} {@0 ps qs : Patterns (argsTy (dataDefs sig d0) c)} {@0 v : Value (TyData d0)}
  → ps ⊆* qs
  → con c qs ≼ v
  → con c ps ≼ v
subsumes : {@0 ps qs : Patterns αs0} {@0 vs : Values αs0}
  → ps ⊆* qs
  → qs ≼* vs
  → ps ≼* vs

subsume —⊆         i = —≼
subsume (con⊆ ss)  i = subsumeConCase ss i
subsume (∣⊆ˡ s)    i = ∣≼ˡ (subsume s i)
subsume (∣⊆ʳ s)    i = ∣≼ʳ (subsume s i)

subsumeConCase ss (con≼ is) = con≼ (subsumes ss is)

subsumes []       []       = []
subsumes (s ∷ ss) (i ∷ is) = subsume s i ∷ subsumes ss is

{-# COMPILE AGDA2HS subsume        #-}
{-# COMPILE AGDA2HS subsumeConCase #-}
{-# COMPILE AGDA2HS subsumes       #-}
