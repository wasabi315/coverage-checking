open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm
open import CoverageCheck.Usefulness.Properties

module CoverageCheck.Usefulness.UsefulP
  ⦃ @0 globals : Globals ⦄
  where

-- agda2hs does not import class methods for some reason, so we need to import them manually
{-# FOREIGN AGDA2HS
import CoverageCheck.Usefulness.Algorithm
#-}

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Usefulness

module _ ⦃ @0 sig : Signature ⦄ (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) where

  -- ps is useful with respect to P iff there exists a pattern vector qs such that
  --   1. there exists a value vector vs that matches qs
  --   2. all rows of P are disjoint from qs
  --   3. ps subsumes qs
  record UsefulP' : Type where
    constructor ⟪_,_,_,_⟫
    field
      qs       : Patterns αs0
      @0 {vs}     : Values αs0
      @0 qs≼vs : qs ≼* vs
      @0 P#qs  : P #** qs
      @0 ps⊆qs : ps ⊆* qs

  open UsefulP'

  record UsefulP : Type where
    constructor MkUsefulP
    field
      witnesses : NonEmpty UsefulP'

  open UsefulP public

  {-# COMPILE AGDA2HS UsefulP' unboxed #-}
  {-# COMPILE AGDA2HS UsefulP  newtype #-}

--------------------------------------------------------------------------------
-- Properties of usefulness


module _ ⦃ @0 sig : Signature ⦄ where

  usefulPNilOkCase : UsefulP [] ⌈⌉
  usefulPNilOkCase = MkUsefulP (⟪ ⌈⌉ , ⌈⌉ , (λ ()) , ⌈⌉ ⟫ ◂ [])
  {-# COMPILE AGDA2HS usefulPNilOkCase #-}

  usefulPNilBadCase : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ UsefulP (ps ∷ P) ⌈⌉
  usefulPNilBadCase {ps = ⌈⌉} (MkUsefulP (⟪ ⌈⌉ , _ , h , _ ⟫ ◂ _)) =
    contradiction ⌈⌉ (h (here ⌈⌉))


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulPOrCaseL' : UsefulP' P (r₁ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseL' ⟪ q ◂ qs , inh , disj , s ◂ ss ⟫ =
    ⟪ q ◂ qs , inh , disj , ∣⊆ˡ s ◂ ss ⟫
  {-# COMPILE AGDA2HS usefulPOrCaseL' transparent #-}

  usefulPOrCaseList : List (UsefulP' P (r₁ ◂ ps)) → List (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseList []       = []
  usefulPOrCaseList (h ∷ hs) = usefulPOrCaseL' h ∷ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseList transparent #-}

  usefulPOrCaseL : NonEmpty (UsefulP' P (r₁ ◂ ps)) → NonEmpty (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseL (h ◂ hs) = usefulPOrCaseL' h ◂ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseL transparent #-}

  usefulPOrCaseR' : UsefulP' P (r₂ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseR' ⟪ q ◂ qs , inh , disj , s ◂ ss ⟫ =
    ⟪ q ◂ qs , inh , disj , ∣⊆ʳ s ◂ ss ⟫
  {-# COMPILE AGDA2HS usefulPOrCaseR' transparent #-}

  usefulPOrCaseRList : List (UsefulP' P (r₂ ◂ ps)) → List (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseRList []       = []
  usefulPOrCaseRList (h ∷ hs) = usefulPOrCaseR' h ∷ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseRList transparent #-}

  usefulPOrCaseR : NonEmpty (UsefulP' P (r₂ ◂ ps)) → NonEmpty (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseR (h ◂ hs) = usefulPOrCaseR' h ◂ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseR transparent #-}

  usefulPOrCase : These (UsefulP P (r₁ ◂ ps)) (UsefulP P (r₂ ◂ ps)) → UsefulP P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCase (This (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseL hs)
  usefulPOrCase (That (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseR hs)
  usefulPOrCase (Both (MkUsefulP hs) (MkUsefulP hs')) = MkUsefulP (usefulPOrCaseL hs <> usefulPOrCaseR hs')
  {-# COMPILE AGDA2HS usefulPOrCase #-}

  @0 usefulPOrCaseInv' : UsefulP' P (r₁ ∣ r₂ ◂ ps) → Either (UsefulP' P (r₁ ◂ ps)) (UsefulP' P (r₂ ◂ ps))
  usefulPOrCaseInv' ⟪ qs , inh , disj , ∣⊆ˡ s ◂ ss ⟫ =
    Left (⟪ qs , inh , disj , s ◂ ss ⟫)
  usefulPOrCaseInv' ⟪ qs , inh , disj , ∣⊆ʳ s ◂ ss ⟫ =
    Right (⟪ qs , inh , disj , s ◂ ss ⟫)

  @0 usefulPOrCaseInv : UsefulP P (r₁ ∣ r₂ ◂ ps) → These (UsefulP P (r₁ ◂ ps)) (UsefulP P (r₂ ◂ ps))
  usefulPOrCaseInv (MkUsefulP hs) = mapThese MkUsefulP MkUsefulP
    (partitionEithersNonEmpty (fmap usefulPOrCaseInv' hs))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {c : NameCon d} {@0 rs : Patterns (argsTy (dataDefs sig d) c)} {@0 ps : Patterns αs0} where

  usefulPConCase' : UsefulP' (specialize c P) (rs ◂◂ᵖ ps) → UsefulP' P (con c rs ◂ ps)
  usefulPConCase' ⟪ qs , is , disj , ss ⟫ =
    case splitSubsumptions rs ss of λ where
      ((qs₁ , qs₂) ⟨ refl , (ss₁ , ss₂) ⟩) →
        let @0 h : ∃[ vs ∈ _ ] (con c qs₁ ◂ qs₂ ≼* vs)
            h = case splitInstances qs₁ is of λ where
              (_ ⟨ refl , (is₁ , is₂) ⟩) → _ ⟨ con≼ is₁ ◂ is₂ ⟩
         in ⟪ con c qs₁ ◂ qs₂
            , proof h
            , specialize-preserves-#**⁻ disj
            , con⊆ ss₁ ◂ ss₂ ⟫

  {-# COMPILE AGDA2HS usefulPConCase' #-}

  usefulPConCase : UsefulP (specialize c P) (rs ◂◂ᵖ ps) → UsefulP P (con c rs ◂ ps)
  usefulPConCase (MkUsefulP hs) = MkUsefulP (fmap usefulPConCase' hs)
  {-# COMPILE AGDA2HS usefulPConCase #-}


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulPConCaseInv' : UsefulP' P (con c rs ◂ ps) → UsefulP' (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv' ⟪ con c qs' ◂ qs , con≼ is' ◂ is , disj , con⊆ ss' ◂ ss ⟫ =
    ⟪ qs' ◂◂ᵖ qs , is' ◂◂ⁱ is , specialize-preserves-#** disj , ss' ◂◂ˢ ss ⟫

  usefulPConCaseInv : UsefulP P (con c rs ◂ ps) → UsefulP (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv (MkUsefulP hs) = MkUsefulP (fmap usefulPConCaseInv' hs)


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  where

  usefulPWildCompCase' : (c : NameCon d)
    → UsefulP' (specialize c P) (—* ◂◂ᵖ ps)
    → UsefulP' P (— ◂ ps)
  usefulPWildCompCase' c ⟪ qs , is , disj , ss ⟫ =
    case splitSubsumptions {αs = argsTy (dataDefs sig d) c} —* ss of λ where
      ((qs₁ , qs₂) ⟨ refl , (ss₁ , ss₂) ⟩) →
        let @0 h : ∃[ vs ∈ _ ] (con c qs₁ ◂ qs₂ ≼* vs)
            h = case splitInstances qs₁ is of λ where
              (_ ⟨ refl , (is₁ , is₂) ⟩) → _ ⟨ con≼ is₁ ◂ is₂ ⟩
         in ⟪ con c qs₁ ◂ qs₂
            , proof h
            , specialize-preserves-#**⁻ disj
            , —⊆ ◂ ss₂ ⟫
  {-# COMPILE AGDA2HS usefulPWildCompCase' #-}

  usefulPWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
    → UsefulP P (— ◂ ps)
  usefulPWildCompCase hs = MkUsefulP do
    (c , MkUsefulP hs') ← hs
    fmap (usefulPWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulPWildCompCase #-}

  @0 usefulPWildCompCaseInv' : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → (qs : Patterns (TyData d ◂ αs0)) {vs : Values (TyData d ◂ αs0)}
    → @0 qs ≼* vs
    → @0 P #** qs
    → @0 (— ◂ ps) ⊆* qs
    → Σ[ c ∈ NameCon d ] UsefulP' (specialize c P) (—* ◂◂ᵖ ps)
  usefulPWildCompCaseInv' (— ◂ qs) (—≼ ◂ is) disj (_ ◂ ss) =
    ( inhabCon
    , ⟪ —* ◂◂ᵖ qs
      , iWilds {vs = inhabArgs} ◂◂ⁱ is
      , specialize-preserves-#**-wild disj
      , —⊆* ◂◂ˢ ss ⟫)
  usefulPWildCompCaseInv' (con c qs' ◂ qs) (con≼ is' ◂ is) disj (s ◂ ss) =
    ( c
    , ⟪ qs' ◂◂ᵖ qs
      , is' ◂◂ⁱ is
      , specialize-preserves-#** disj
      , —⊆* ◂◂ˢ ss ⟫)
  usefulPWildCompCaseInv' (q₁ ∣ q₂ ◂ qs) (∣≼ˡ i ◂ is) disj (SCons s ss) =
    usefulPWildCompCaseInv' (q₁ ◂ qs) (i ◂ is) (#-∣ˡ disj) (—⊆ ◂ ss)
  usefulPWildCompCaseInv' (q₁ ∣ q₂ ◂ qs) (∣≼ʳ i ◂ is) disj (SCons s ss) =
    usefulPWildCompCaseInv' (q₂ ◂ qs) (i ◂ is) (#-∣ʳ disj) (—⊆ ◂ ss)

  @0 usefulPWildCompCaseInv : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → UsefulP P (— ◂ ps)
    → NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
  usefulPWildCompCaseInv (MkUsefulP hs) = do
    ⟪ qs , is , disj , ss ⟫ ← hs
    let (c , h') = usefulPWildCompCaseInv' qs is disj ss
    pure (c , MkUsefulP (h' ◂ []))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  usefulPWildMissCase' :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP' (default_ P) ps
    → NonEmpty (UsefulP' P (— ◂ ps))
  usefulPWildMissCase' (Left (Erased h)) ⟪ qs , is , disj , ss ⟫ =
    ⟪ — ◂ qs
    , IWild {v = inhab} ◂ is
    , default-preserves-#**⁻-wild h disj
    , —⊆ ◂ ss ⟫ ◂ []
  usefulPWildMissCase' (Right hs) ⟪ qs , is , disj , ss ⟫ =
    fmap
      (λ where
        (c ⟨ h ⟩) →
          ⟪ con c —* ◂ qs
          , con≼ (iWilds {vs = tabulateValues λ _ → nonEmptyAxiom}) ◂ is
          , default-preserves-#**⁻ h disj
          , —⊆ ◂ ss ⟫
          )
      hs
  {-# COMPILE AGDA2HS usefulPWildMissCase' #-}

  usefulPWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP (default_ P) ps → UsefulP P (— ◂ ps)
  usefulPWildMissCase h (MkUsefulP hs) =
    MkUsefulP (hs >>= usefulPWildMissCase' h)
  {-# COMPILE AGDA2HS usefulPWildMissCase #-}

  usefulPWildMissCaseInv' : UsefulP' P (— ◂ ps) → UsefulP' (default_ P) ps
  usefulPWildMissCaseInv' ⟪ q ◂ qs , i ◂ is , disj , s ◂ ss ⟫ =
    ⟪ qs , is , default-preserves-#** disj , ss ⟫

  usefulPWildMissCaseInv : UsefulP P (— ◂ ps) → UsefulP (default_ P) ps
  usefulPWildMissCaseInv (MkUsefulP hs) =
    MkUsefulP (fmap usefulPWildMissCaseInv' hs)

--------------------------------------------------------------------------------

instance iUsefulPUseful : Usefulness UsefulP
iUsefulPUseful .nilOkCase       = usefulPNilOkCase
iUsefulPUseful .nilBadCase      = usefulPNilBadCase
iUsefulPUseful .orCase          = usefulPOrCase
iUsefulPUseful .orCaseInv       = usefulPOrCaseInv
iUsefulPUseful .conCase         = usefulPConCase
iUsefulPUseful .conCaseInv      = usefulPConCaseInv
iUsefulPUseful .wildMissCase    = usefulPWildMissCase
iUsefulPUseful .wildMissCaseInv = λ _ → usefulPWildMissCaseInv
iUsefulPUseful .wildCompCase    = λ _ → usefulPWildCompCase
iUsefulPUseful .wildCompCaseInv = λ _ → usefulPWildCompCaseInv
{-# COMPILE AGDA2HS iUsefulPUseful #-}
