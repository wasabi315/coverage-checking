open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Instance

module CoverageCheck.BranchSelection
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

infixr 5 _◂_ appendBranchSelections
infix  4 BranchSelection BranchSelections _⊈_ _⊈*_

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Branch selection

data BranchSelection  : (@0 p q : Pattern α0)     → Type
data BranchSelections : (@0 ps qs : Patterns αs0) → Type

syntax BranchSelection  p  q  = p ⊆ q
syntax BranchSelections ps qs = ps ⊆* qs

-- p ⊆ q : q can be obtained from p by selecting branches of or-patterns
data BranchSelection where
  BWild : BranchSelection {α0} — —

  BCon : {c : NameCon d0}
    (let @0 αs : Tys
         αs = argsTy (dataDefs sig d0) c)
    {@0 ps qs : Patterns αs}
    → (bs : ps ⊆* qs)
    → con c ps ⊆ con c qs

  BOrL : {@0 p q r : Pattern α0}
    → (b : p ⊆ r)
    → (p ∣ q) ⊆ r

  BOrR : {@0 p q r : Pattern α0}
    → (b : q ⊆ r)
    → (p ∣ q) ⊆ r

{-# COMPILE AGDA2HS BranchSelection deriving Show #-}

pattern —⊆      = BWild
pattern con⊆ bs = BCon bs
pattern ∣⊆ˡ b   = BOrL b
pattern ∣⊆ʳ b   = BOrR b

data BranchSelections where
  BNil : ⌈⌉ ⊆* ⌈⌉
  BCons : {@0 p q : Pattern α0} {@0 ps qs : Patterns αs0}
    → (b : p ⊆ q)
    → (bs : ps ⊆* qs)
    → (p ◂ ps) ⊆* (q ◂ qs)

{-# COMPILE AGDA2HS BranchSelections deriving Show #-}

pattern ⌈⌉       = BNil
pattern _◂_ b bs = BCons b bs

_⊈_ : (@0 p q : Pattern α0) → Type
p ⊈ q = ¬ p ⊆ q

_⊈*_ : (@0 ps qs : Patterns αs0) → Type
qs ⊈* ps = ¬ ps ⊆* qs

--------------------------------------------------------------------------------
-- Properties of the branch selection relation

bWilds : BranchSelections {αs} —* —*
bWilds {⌈⌉}     = ⌈⌉
bWilds {α ◂ αs} = —⊆ ◂ bWilds
{-# COMPILE AGDA2HS bWilds #-}
syntax bWilds = —⊆*

module _ {@0 p q r : Pattern α0} where

  bOrInv : (p ∣ q ⊆ r) → Either (p ⊆ r) (q ⊆ r)
  bOrInv (∣⊆ˡ b) = Left b
  bOrInv (∣⊆ʳ b) = Right b
  {-# COMPILE AGDA2HS bOrInv #-}
  syntax bOrInv = ∣⊆⁻


module _ {@0 c : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c)
  {@0 ps qs : Patterns αs}
  where

  bConInv : (con c ps ⊆ con c qs) → ps ⊆* qs
  bConInv (con⊆ bs) = bs
  {-# COMPILE AGDA2HS bConInv #-}
  syntax bConInv = con⊆⁻


module _ {@0 p q : Pattern α0} {@0 ps qs : Patterns αs0} where

  bUncons : (p ◂ ps ⊆* q ◂ qs) → (p ⊆ q) × (ps ⊆* qs)
  bUncons (b ◂ bs) = b , bs
  {-# COMPILE AGDA2HS bUncons #-}
  syntax bUncons = ◂⊆⁻


appendBranchSelections : {@0 ps ps' : Patterns αs0} {@0 qs qs' : Patterns βs0}
  → (ps ⊆* ps')
  → (qs ⊆* qs')
  → (ps ◂◂ᵖ qs) ⊆* (ps' ◂◂ᵖ qs')
appendBranchSelections ⌈⌉ bs' = bs'
appendBranchSelections (b ◂ bs) bs' = b ◂ appendBranchSelections bs bs'
{-# COMPILE AGDA2HS appendBranchSelections #-}
syntax appendBranchSelections bs bs' = bs ◂◂ᵇ bs'

unappendBranchSelections : (ps : Patterns αs0) {@0 ps' : Patterns αs0} {@0 qs qs' : Patterns βs0}
  → (ps ◂◂ᵖ qs) ⊆* (ps' ◂◂ᵖ qs')
  → (ps ⊆* ps') × (qs ⊆* qs')
unappendBranchSelections ⌈⌉       {⌈⌉}    bs       = ⌈⌉ , bs
unappendBranchSelections (p ◂ ps) {_ ◂ _} (b ◂ bs) = first (b ◂_) (unappendBranchSelections ps bs)
{-# COMPILE AGDA2HS unappendBranchSelections #-}
syntax unappendBranchSelections ps bs = ps ◂◂ᵇ⁻ bs

splitBranchSelections : (@0 ps : Patterns αs) {@0 qs : Patterns βs0} {rs : Patterns (αs ◂◂ βs0)}
  → @0 (ps ◂◂ᵖ qs) ⊆* rs
  → ∃[ (rs₁ , rs₂) ∈ (Patterns αs × Patterns βs0) ] (rs₁ ◂◂ᵖ rs₂ ≡ rs) × ((ps ⊆* rs₁) × (qs ⊆* rs₂))
splitBranchSelections {αs = ⌈⌉} ⌈⌉ {rs = rs} bs = (⌈⌉ , rs) ⟨ refl , (⌈⌉ , bs) ⟩
splitBranchSelections {αs = α ◂ αs} (p ◂ ps) {rs = r ◂ rs} (b ◂ bs) =
  let rs₁rs₂ ⟨ eq , bs' ⟩ = splitBranchSelections ps bs in
  first (r ◂_) rs₁rs₂ ⟨ cong (r ◂_) eq , first (b ◂_) bs' ⟩
{-# COMPILE AGDA2HS splitBranchSelections #-}

-- module _ {@0 ps : Patterns αs0} {@0 vs : Values αs0} {@0 u : Value β0} {@0 us : Values βs} where

--   wildHeadLemma : (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs) → (— ◂ ps) ≼* (u ◂ vs)
--   wildHeadLemma h = case unappendInstances —* h of λ where
--     (_ , h') → —≼ ◂ h'
--   {-# COMPILE AGDA2HS wildHeadLemma #-}

--   wildHeadLemmaInv : (— ◂ ps) ≼* (u ◂ vs) → (—* ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
--   wildHeadLemmaInv (—≼ ◂ h) = —≼* ◂◂ⁱ h
--   {-# COMPILE AGDA2HS wildHeadLemmaInv #-}


-- module _ {@0 p q : Pattern α0} {@0 ps : Patterns αs0} {@0 v : Value α0} {@0 vs : Values αs0} where

--   orHeadLemma : Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
--     → (p ∣ q ◂ ps) ≼* (v ◂ vs)
--   orHeadLemma (Left (h ◂ hs))  = ∣≼ˡ h ◂ hs
--   orHeadLemma (Right (h ◂ hs)) = ∣≼ʳ h ◂ hs
--   {-# COMPILE AGDA2HS orHeadLemma #-}

--   orHeadLemmaInv : (p ∣ q ◂ ps) ≼* (v ◂ vs)
--     → Either (p ◂ ps ≼* v ◂ vs) (q ◂ ps ≼* v ◂ vs)
--   orHeadLemmaInv (∣≼ˡ h ◂ hs) = Left (h ◂ hs)
--   orHeadLemmaInv (∣≼ʳ h ◂ hs) = Right (h ◂ hs)
--   {-# COMPILE AGDA2HS orHeadLemmaInv #-}


-- module _ {c : NameCon d0}
--   (let @0 αs : Tys
--        αs = argsTy (dataDefs sig d0) c)
--   {rs : Patterns αs} {@0 ps : Patterns βs0}
--   {@0 us : Values αs} {@0 vs : Values βs0}
--   where

--   conHeadLemma : (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
--     → (con c rs ◂ ps) ≼* (con c us ◂ vs)
--   conHeadLemma h = case unappendInstances rs h of λ where
--     (h1 , h2) → con≼ h1 ◂ h2
--   {-# COMPILE AGDA2HS conHeadLemma #-}


-- module _ {@0 c : NameCon d0}
--   (let @0 αs : Tys
--        αs = argsTy (dataDefs sig d0) c)
--   {rs : Patterns αs} {@0 ps : Patterns βs0}
--   {@0 us : Values αs} {@0 vs : Values βs0}
--   where

--   conHeadLemmaInv : (con c rs ◂ ps) ≼* (con c us ◂ vs)
--     → (rs ◂◂ᵖ ps) ≼* (us ◂◂ᵛ vs)
--   conHeadLemmaInv (con≼ h ◂ h') = h ◂◂ⁱ h'
--   {-# COMPILE AGDA2HS conHeadLemmaInv #-}


module _ {c c' : NameCon d0}
  (let @0 αs : Tys
       αs = argsTy (dataDefs sig d0) c
       @0 αs' : Tys
       αs' = argsTy (dataDefs sig d0) c')
  {@0 ps : Patterns αs} {@0 qs : Patterns αs'}
  where

  c⊆c'⇒c≡c' : con c ps ⊆ con c' qs → c ≡ c'
  c⊆c'⇒c≡c' (con⊆ h) = refl


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

subsume —⊆        i = —≼
subsume (con⊆ bs) i = subsumeConCase bs i
subsume (∣⊆ˡ b)   i = ∣≼ˡ (subsume b i)
subsume (∣⊆ʳ b)   i = ∣≼ʳ (subsume b i)

subsumeConCase bs (con≼ is) = con≼ (subsumes bs is)

subsumes ⌈⌉       ⌈⌉       = ⌈⌉
subsumes (b ◂ bs) (i ◂ is) = subsume b i ◂ subsumes bs is

{-# COMPILE AGDA2HS subsume        #-}
{-# COMPILE AGDA2HS subsumeConCase #-}
{-# COMPILE AGDA2HS subsumes       #-}
