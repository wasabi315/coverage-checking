open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax

module CoverageCheck.Instance
  {{@0 globals : Globals}}
  {{@0 sig : Signature}}
  where

private open module @0 G = Globals globals

infixr 5 _◂_ appendInstances
infix  4 Instance Instances InstanceMatrix
         NonInstance NonInstances NonInstanceMatrix
         decInstance decInstances

private
  variable
    @0 α β : Type
    @0 αs βs : Types

--------------------------------------------------------------------------------
-- Instance relation

data Instance  : (@0 p : Pattern α) (@0 v : Value α) → Set
data Instances : (@0 ps : Patterns αs) (@0 vs : Values αs) → Set

syntax Instance  p  v  = p ≼ v
syntax Instances ps vs = ps ≼* vs

-- p ≼ v : pattern p matches value v
data Instance where
  IWild : {@0 v : Value α} → — ≼ v

  ICon : {@0 d : NameData} {c : NameCon d}
    (let @0 αs : Types
         αs = argsTy (dataDefs sig d) c)
    {@0 ps : Patterns αs}
    {@0 vs : Values αs}
    → (is : ps ≼* vs)
    → con c ps ≼ con c vs

  IOrL : ∀ {@0 p q : Pattern α} {@0 v}
    → (i : p ≼ v)
    → (p ∣ q) ≼ v

  IOrR : ∀ {@0 p q : Pattern α} {@0 v}
    → (i : q ≼ v)
    → (p ∣ q) ≼ v

pattern —≼      = IWild
pattern con≼ is = ICon {c = _} is
pattern ∣≼ˡ i   = IOrL i
pattern ∣≼ʳ i   = IOrR i

-- ps ≼* vs : each pattern in ps matches the corresponding value in vs
data Instances where
  INil  : ⌈⌉ ≼* ⌈⌉
  ICons : ∀ {@0 p : Pattern α} {@0 v} {@0 ps : Patterns αs} {@0 vs}
    → (p≼v : p ≼ v)
    → (ps≼vs : ps ≼* vs)
    → (p ◂ ps) ≼* (v ◂ vs)

pattern ⌈⌉       = INil
pattern _◂_ i is = ICons i is
{-# COMPILE AGDA2HS Instance  deriving Show #-}
{-# COMPILE AGDA2HS Instances deriving Show #-}

InstanceMatrix : (@0 P : PatternMatrix αs) (@0 vs : Values αs) → Set
syntax InstanceMatrix P vs = P ≼** vs
P ≼** vs = Any (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS InstanceMatrix #-}

NonInstance : (@0 p : Pattern α) (@0 v : Value α) → Set
NonInstance p v = p ≼ v → ⊥
syntax NonInstance p v = p ⋠ v

NonInstances : (@0 ps : Patterns αs) (@0 vs : Values αs) → Set
NonInstances ps vs = ps ≼* vs → ⊥
syntax NonInstances ps vs = ps ⋠* vs

NonInstanceMatrix : (@0 P : PatternMatrix αs) (@0 vs : Values αs) → Set
NonInstanceMatrix P vs = P ≼** vs → ⊥
syntax NonInstanceMatrix P vs = P ⋠** vs

--------------------------------------------------------------------------------
-- Properties of the instance relation

-- αs is not erasable
iWilds : ∀ {αs} {@0 vs : Values αs} → —* ≼* vs
syntax iWilds = —≼*
—≼* {⌈⌉}     {⌈⌉}     = ⌈⌉
—≼* {α ◂ αs} {v ◂ vs} = —≼ ◂ —≼*
{-# COMPILE AGDA2HS iWilds #-}

module _ {@0 p q : Pattern α} {@0 v} where

  iOrInv : (p ∣ q ≼ v) → Either (p ≼ v) (q ≼ v)
  syntax iOrInv = ∣≼⁻
  ∣≼⁻ (∣≼ˡ h) = Left h
  ∣≼⁻ (∣≼ʳ h) = Right h
  {-# COMPILE AGDA2HS iOrInv #-}


module _ {@0 d : NameData} {@0 c : NameCon d}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d) c)
  {@0 ps : Patterns αs}
  {@0 vs : Values αs}
  where

  iConInv : (con c ps ≼ con c vs) → ps ≼* vs
  syntax iConInv = con≼⁻
  con≼⁻ (con≼ is) = is
  {-# COMPILE AGDA2HS iConInv #-}

module _ {@0 p : Pattern α} {@0 v} {@0 ps : Patterns αs} {@0 vs} where

  iUncons : (p ◂ ps ≼* v ◂ vs) → (p ≼ v) × (ps ≼* vs)
  syntax iUncons = ◂ⁱ⁻
  ◂ⁱ⁻ (i ◂ is) = i , is
  {-# COMPILE AGDA2HS iUncons #-}


appendInstances : ∀ {@0 ps : Patterns αs} {@0 us} {@0 qs : Patterns βs} {@0 vs}
  → ps ≼* us
  → qs ≼* vs
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
syntax appendInstances is1 is2 = is1 ◂◂ⁱ is2
⌈⌉         ◂◂ⁱ is2 = is2
(i1 ◂ is1) ◂◂ⁱ is2 = i1 ◂ appendInstances is1 is2
{-# COMPILE AGDA2HS appendInstances #-}

-- ps is not erasable
unappendInstances : ∀ (ps : Patterns αs) {@0 us} {@0 qs : Patterns βs} {@0 vs}
  → (ps ◂◂ᵖ qs) ≼* (us ◂◂ᵛ vs)
  → (ps ≼* us) × (qs ≼* vs)
unappendInstances ⌈⌉       {⌈⌉}    is       = ⌈⌉ , is
unappendInstances (p ◂ ps) {_ ◂ _} (i ◂ is) = first (i ◂_) (unappendInstances ps is)
{-# COMPILE AGDA2HS unappendInstances #-}

-- αs is not erasable
splitInstances : ∀ (ps : Patterns αs) {@0 qs : Patterns βs} {@0 us : Values (αs ◂◂ βs)}
  → (ps ◂◂ᵖ qs) ≼* us
  → Σ0[ vs ∈ _ ] Σ0[ ws ∈ _ ] Σ0[ _ ∈ ((vs ◂◂ᵛ ws) ≡ us) ] (ps ≼* vs × qs ≼* ws)
splitInstances ⌈⌉                     is       = < < ⟨ refl ⟩ (⌈⌉ , is) > >
splitInstances (p ◂ ps) {us = u ◂ us} (i ◂ is) =
  let < < ⟨ eq ⟩ is' > > = splitInstances ps is in
  < < ⟨ cong (u ◂_) eq ⟩ first (i ◂_) is' > >
{-# COMPILE AGDA2HS splitInstances #-}

-- βs is not erasable
module _ {@0 αs} {βs} {@0 ps : Patterns αs} {@0 u : Value β} {@0 us : Values βs} {@0 vs} where

  wildHeadLemma : (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (— ◂ ps) ≼* (u ◂ vs)
  wildHeadLemma h =
    let _ , h' = unappendInstances —* h in
    —≼ ◂ h'
  {-# COMPILE AGDA2HS wildHeadLemma #-}

  wildHeadLemmaInv : (— ◂ ps) ≼* (u ◂ vs) → (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
  wildHeadLemmaInv (—≼ ◂ h) = —≼* ◂◂ⁱ h
  {-# COMPILE AGDA2HS wildHeadLemmaInv #-}


module _ {@0 p q : Pattern α} {@0 ps : Patterns αs} {@0 v} {@0 vs} where

  orHeadLemma : Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs) → (p ∣ q ◂ ps) ≼* (v ◂ vs)
  orHeadLemma (Left (h ◂ hs))  = ∣≼ˡ h ◂ hs
  orHeadLemma (Right (h ◂ hs)) = ∣≼ʳ h ◂ hs
  {-# COMPILE AGDA2HS orHeadLemma #-}

  orHeadLemmaInv : (p ∣ q ◂ ps) ≼* (v ◂ vs) → Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
  orHeadLemmaInv (∣≼ˡ h ◂ hs) = Left (h ◂ hs)
  orHeadLemmaInv (∣≼ʳ h ◂ hs) = Right (h ◂ hs)
  {-# COMPILE AGDA2HS orHeadLemmaInv #-}


-- rs is not erasable
module _ {@0 d : NameData} {c : NameCon d}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d) c)
  {rs : Patterns αs}
  {@0 ps : Patterns βs}
  {@0 us : Values αs}
  {@0 vs : Values βs}
  where

  conHeadLemma : (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (con c rs ◂ ps) ≼* (con c us ◂ vs)
  conHeadLemma h =
    let h1 , h2 = unappendInstances rs h in
    con≼ h1 ◂ h2
  {-# COMPILE AGDA2HS conHeadLemma #-}

  conHeadLemmaInv : (con c rs ◂ ps) ≼* (con c us ◂ vs) → (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
  conHeadLemmaInv (con≼ h ◂ h') = h ◂◂ⁱ h'
  {-# COMPILE AGDA2HS conHeadLemmaInv #-}


module _ {d : NameData} {c c' : NameCon d}
  (let @0 αs : Types
       αs = argsTy (dataDefs sig d) c
       @0 αs' : Types
       αs' = argsTy (dataDefs sig d) c')
  {@0 ps : Patterns αs}
  {@0 vs : Values αs'}
  where

  c≼c'⇒c≡c' : con c ps ≼ con c' vs → c ≡ c'
  c≼c'⇒c≡c' (con≼ h) = refl

--------------------------------------------------------------------------------
-- Pattern matching

decInstance    : (p : Pattern α) (v : Value α) → Dec (p ≼ v)
decInstances   : (ps : Patterns αs) (vs : Values αs) → Dec (ps ≼* vs)

syntax decInstance  p  v  = p ≼? v
syntax decInstances ps vs = ps ≼*? vs

con c ps ≼? con c' vs = ifDec0 (c ≟ c')
  (λ where {{refl}} → mapDec con≼ con≼⁻ (ps ≼*? vs))
  (λ {{h}} → No (contraposition c≼c'⇒c≡c' h))
—       ≼? v = Yes —≼
(p ∣ q) ≼? v = mapDec (either ∣≼ˡ ∣≼ʳ) ∣≼⁻ (eitherDec (p ≼? v) (q ≼? v))

⌈⌉       ≼*? ⌈⌉       = Yes ⌈⌉
(p ◂ ps) ≼*? (v ◂ vs) = mapDec (uncurry _◂_) ◂ⁱ⁻ (p ≼? v ×-dec ps ≼*? vs)

{-# COMPILE AGDA2HS decInstance   #-}
{-# COMPILE AGDA2HS decInstances  #-}

Match : (@0 P : PatternMatrix αs) (@0 vs : Values αs) → Set
Match P vs = First (λ ps → ps ≼* vs) P
{-# COMPILE AGDA2HS Match #-}

decMatch : (P : PatternMatrix αs) (vs : Values αs) → Dec (Match P vs)
decMatch p vs = firstDec (λ ps → ps ≼*? vs) p
{-# COMPILE AGDA2HS decMatch #-}
