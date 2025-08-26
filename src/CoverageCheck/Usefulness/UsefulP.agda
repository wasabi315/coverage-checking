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

  UsefulP' : Type
  UsefulP' = ∃[ qs ∈ Patterns αs0 ] (P #** qs) × (ps ⊆* qs)

  record UsefulP : Type where
    constructor MkUsefulP
    field
      witnesses : NonEmpty UsefulP'

  open UsefulP  public

  {-# COMPILE AGDA2HS UsefulP' inline  #-}
  {-# COMPILE AGDA2HS UsefulP  newtype #-}

--------------------------------------------------------------------------------
-- Properties of usefulness


module _ ⦃ @0 sig : Signature ⦄ where

  usefulPNilOkCase : UsefulP [] ⌈⌉
  usefulPNilOkCase = MkUsefulP ((⌈⌉ ⟨ (λ ()) , ⌈⌉ ⟩) ◂ [])
  {-# COMPILE AGDA2HS usefulPNilOkCase #-}

  usefulPNilBadCase : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ UsefulP (ps ∷ P) ⌈⌉
  usefulPNilBadCase {ps = ⌈⌉} (MkUsefulP ((⌈⌉ ⟨ h , _ ⟩) ◂ _)) =
    contradiction ⌈⌉ (h (here ⌈⌉))


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulPOrCaseL' : UsefulP' P (r₁ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseL' ((q ◂ qs) ⟨ disj , s ◂ ss ⟩) =
    (q ◂ qs) ⟨ disj , (∣⊆ˡ s ◂ ss) ⟩
  {-# COMPILE AGDA2HS usefulPOrCaseL' transparent #-}

  usefulPOrCaseList : List (UsefulP' P (r₁ ◂ ps)) → List (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseList []       = []
  usefulPOrCaseList (h ∷ hs) = usefulPOrCaseL' h ∷ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseList transparent #-}

  usefulPOrCaseL : NonEmpty (UsefulP' P (r₁ ◂ ps)) → NonEmpty (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseL (h ◂ hs) = usefulPOrCaseL' h ◂ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseL transparent #-}

  usefulPOrCaseR' : UsefulP' P (r₂ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseR' ((q ◂ qs) ⟨ disj , s ◂ ss ⟩) =
    (q ◂ qs) ⟨ disj , (∣⊆ʳ s ◂ ss) ⟩
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
  usefulPOrCaseInv' (qs ⟨ disj , ∣⊆ˡ s ◂ ss ⟩) = Left (qs ⟨ disj , s ◂ ss ⟩)
  usefulPOrCaseInv' (qs ⟨ disj , ∣⊆ʳ s ◂ ss ⟩) = Right (qs ⟨ disj , s ◂ ss ⟩)

  @0 usefulPOrCaseInv : UsefulP P (r₁ ∣ r₂ ◂ ps) → These (UsefulP P (r₁ ◂ ps)) (UsefulP P (r₂ ◂ ps))
  usefulPOrCaseInv (MkUsefulP hs) = mapThese MkUsefulP MkUsefulP
    (partitionEithersNonEmpty (fmap usefulPOrCaseInv' hs))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {c : NameCon d} {@0 rs : Patterns (argsTy (dataDefs sig d) c)} {@0 ps : Patterns αs0} where

  usefulPConCase' : UsefulP' (specialize c P) (rs ◂◂ᵖ ps) → UsefulP' P (con c rs ◂ ps)
  usefulPConCase' (qs ⟨ disj , ss ⟩) =
    case splitSubsumptions rs ss of λ where
      ((qs₁ , qs₂) ⟨ refl , (ss₁ , ss₂) ⟩) →
        (con c qs₁ ◂ qs₂) ⟨ specialize-preserves-#**⁻ disj , (con⊆ ss₁ ◂ ss₂) ⟩
  {-# COMPILE AGDA2HS usefulPConCase' #-}

  usefulPConCase : UsefulP (specialize c P) (rs ◂◂ᵖ ps) → UsefulP P (con c rs ◂ ps)
  usefulPConCase (MkUsefulP hs) = MkUsefulP (fmap usefulPConCase' hs)
  {-# COMPILE AGDA2HS usefulPConCase #-}


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulPConCaseInv' : UsefulP' P (con c rs ◂ ps) → UsefulP' (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv' ((con c qs' ◂ qs) ⟨ disj , con⊆ ss' ◂ ss ⟩) =
    (qs' ◂◂ᵖ qs) ⟨ specialize-preserves-#** disj , (ss' ◂◂ᵇ ss) ⟩

  usefulPConCaseInv : UsefulP P (con c rs ◂ ps) → UsefulP (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv (MkUsefulP hs) = MkUsefulP (fmap usefulPConCaseInv' hs)


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  where

  usefulPWildCompCase' : (c : NameCon d)
    → UsefulP' (specialize c P) (—* ◂◂ᵖ ps)
    → UsefulP' P (— ◂ ps)
  usefulPWildCompCase' c (qs ⟨ disj , ss ⟩) =
    case splitSubsumptions {αs = argsTy (dataDefs sig d) c} —* ss of λ where
      ((qs₁ , qs₂) ⟨ refl , (ss₁ , ss₂) ⟩) →
        (con c qs₁ ◂ qs₂) ⟨ specialize-preserves-#**⁻ disj , —⊆ ◂ ss₂ ⟩
  {-# COMPILE AGDA2HS usefulPWildCompCase' #-}

  usefulPWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
    → UsefulP P (— ◂ ps)
  usefulPWildCompCase hs = MkUsefulP do
    (c , MkUsefulP hs') ← hs
    fmap (usefulPWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulPWildCompCase #-}

  usefulPWildCompCaseInv' : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → (qs : Patterns (TyData d ◂ αs0))
    → @0 P #** qs
    → @0 (— ◂ ps) ⊆* qs
    → NonEmpty (Σ[ c ∈ NameCon d ] UsefulP' (specialize c P) (—* ◂◂ᵖ ps))
  usefulPWildCompCaseInv' (— ◂ qs) disj (s ◂ ss) =
    (inhabCon , ((—* ◂◂ᵖ qs) ⟨ (specialize-preserves-#**-wild disj , —⊆* ◂◂ᵇ ss) ⟩)) ◂ []
  usefulPWildCompCaseInv' (con c qs' ◂ qs) disj (s ◂ ss) =
    ((c , ((qs' ◂◂ᵖ qs) ⟨ (specialize-preserves-#** disj , —⊆* ◂◂ᵇ ss) ⟩))) ◂ []
  usefulPWildCompCaseInv' (q₁ ∣ q₂ ◂ qs) disj (s ◂ ss) =
    usefulPWildCompCaseInv' (q₁ ◂ qs) (#-∣ˡ disj) (—⊆ ◂ ss) <>
    usefulPWildCompCaseInv' (q₂ ◂ qs) (#-∣ʳ disj) (—⊆ ◂ ss)

  @0 usefulPWildCompCaseInv : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → UsefulP P (— ◂ ps)
    → NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
  usefulPWildCompCaseInv (MkUsefulP hs) = do
    (qs ⟨ disj , ss ⟩) ← hs
    (c , h') ← usefulPWildCompCaseInv' qs disj ss
    pure (c , MkUsefulP (h' ◂ []))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  usefulPWildMissCase' :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP' (default_ P) ps
    → NonEmpty (UsefulP' P (— ◂ ps))
  usefulPWildMissCase' (Left (Erased h)) (vs ⟨ disj , ss ⟩) =
    ((— ◂ vs) ⟨ default-preserves-#**⁻-wild h disj , (—⊆ ◂ ss) ⟩) ◂ []
  usefulPWildMissCase' (Right hs) (qs ⟨ disj , ss ⟩) =
    fmap
      (λ where
        (c ⟨ h ⟩) → (con c —* ◂ qs) ⟨ default-preserves-#**⁻ h disj , (—⊆ ◂ ss) ⟩)
      hs
  {-# COMPILE AGDA2HS usefulPWildMissCase' #-}

  usefulPWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP (default_ P) ps → UsefulP P (— ◂ ps)
  usefulPWildMissCase h (MkUsefulP hs) =
    MkUsefulP (hs >>= usefulPWildMissCase' h)
  {-# COMPILE AGDA2HS usefulPWildMissCase #-}

  usefulPWildMissCaseInv' : UsefulP' P (— ◂ ps) → UsefulP' (default_ P) ps
  usefulPWildMissCaseInv' ((q ◂ qs) ⟨ disj , s ◂ ss ⟩) =
    qs ⟨ default-preserves-#** disj , ss ⟩

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
