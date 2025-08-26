open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm
open import CoverageCheck.Usefulness.Properties

module CoverageCheck.Usefulness.Useful
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

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
record Useful ⦃ @0 sig : Signature ⦄ (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) : Type where
  constructor MkUseful
  field
    witness       : Values αs0
    @0 P⋠witness  : P ⋠** witness
    @0 ps≼witness : ps ≼* witness
open Useful public
{-# COMPILE AGDA2HS Useful newtype #-}

--------------------------------------------------------------------------------
-- Properties of usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  -- ⌈⌉ is useful wrt []
  usefulNilOkCase : Useful [] ⌈⌉
  usefulNilOkCase = MkUseful ⌈⌉ (λ ()) ⌈⌉
  {-# COMPILE AGDA2HS usefulNilOkCase #-}

  -- [] is not wrt any non-empty matrix
  usefulNilBadCase : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ Useful (ps ∷ P) ⌈⌉
  usefulNilBadCase {⌈⌉} (MkUseful ⌈⌉ h _) = contradiction (here ⌈⌉) h


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulOrCaseL : Useful P (r₁ ◂ ps) → Useful P (r₁ ∣ r₂ ◂ ps)
  usefulOrCaseL (MkUseful (v ◂ vs) nis (i ◂ is)) =
    MkUseful (v ◂ vs) nis (∣≼ˡ i ◂ is)
  {-# COMPILE AGDA2HS usefulOrCaseL transparent #-}

  usefulOrCaseR : Useful P (r₂ ◂ ps) → Useful P (r₁ ∣ r₂ ◂ ps)
  usefulOrCaseR (MkUseful (v ◂ vs) nis (i ◂ is)) =
    MkUseful (v ◂ vs) nis (∣≼ʳ i ◂ is)
  {-# COMPILE AGDA2HS usefulOrCaseR transparent #-}

  usefulOrCase : These (Useful P (r₁ ◂ ps)) (Useful P (r₂ ◂ ps)) → Useful P (r₁ ∣ r₂ ◂ ps)
  usefulOrCase (This h)   = usefulOrCaseL h
  usefulOrCase (That h)   = usefulOrCaseR h
  -- ignore the second argument
  usefulOrCase (Both h _) = usefulOrCaseL h
  {-# COMPILE AGDA2HS usefulOrCase #-}

  @0 usefulOrCaseInv : Useful P (r₁ ∣ r₂ ◂ ps) → These (Useful P (r₁ ◂ ps)) (Useful P (r₂ ◂ ps))
  usefulOrCaseInv (MkUseful vs nis (∣≼ˡ i ◂ is)) = This (MkUseful vs nis (i ◂ is))
  usefulOrCaseInv (MkUseful vs nis (∣≼ʳ i ◂ is)) = That (MkUseful vs nis (i ◂ is))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {c : NameCon d} {@0 rs : Patterns (argsTy (dataDefs sig d) c)} {@0 ps : Patterns αs0} where

  usefulConCase : Useful (specialize c P) (rs ◂◂ᵖ ps) → Useful P (con c rs ◂ ps)
  usefulConCase (MkUseful usvs nis is) = case splitInstances rs is of λ where
    ((us , vs) ⟨ refl , (is1 , is2) ⟩) →
      MkUseful (con c us ◂ vs) (contraposition specialize-preserves-≼ nis) (con≼ is1 ◂ is2)
  {-# COMPILE AGDA2HS usefulConCase #-}


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulConCaseInv : Useful P (con c rs ◂ ps) → Useful (specialize c P) (rs ◂◂ᵖ ps)
  usefulConCaseInv (MkUseful (con c vs ◂ us) nis (con≼ is ◂ is')) =
    MkUseful (vs ◂◂ᵛ us) (contraposition specialize-preserves-≼⁻ nis) (is ◂◂ⁱ is')


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`, `∙ ∷ ps` is also useful wrt P
  usefulWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d ] Useful (specialize c P) (—* ◂◂ᵖ ps))
    → Useful P (— ◂ ps)
  -- only consider the first constructor
  usefulWildCompCase ((c , MkUseful usvs nis is) ◂ _) =
    case splitInstances {αs = argsTy (dataDefs sig d) c} —* is of λ where
      ((us , vs) ⟨ refl , (_ , is') ⟩) →
        MkUseful (con c us ◂ vs) (contraposition specialize-preserves-≼ nis) (—≼ ◂ is')
  {-# COMPILE AGDA2HS usefulWildCompCase #-}

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`
  usefulWildCompCaseInv :
      Useful P (— ◂ ps)
    → NonEmpty (Σ[ c ∈ NameCon d ] Useful (specialize c P) (—* ◂◂ᵖ ps))
  usefulWildCompCaseInv (MkUseful (con c us ◂ vs) nis (_ ◂ is)) =
    (c , MkUseful (us ◂◂ᵛ vs) (contraposition specialize-preserves-≼⁻ nis) (—≼* ◂◂ⁱ is)) ◂ []


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
  usefulWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → Useful (default_ P) ps → Useful P (— ◂ ps)
  -- only consider inhab
  usefulWildMissCase (Left (Erased h)) (MkUseful vs nis is) =
    MkUseful (inhab ◂ vs) (contraposition (default-preserves-≼ (h _)) nis) (—≼ ◂ is)
  -- only consider the first constructor
  usefulWildMissCase (Right (c ⟨ h ⟩ ◂ _)) (MkUseful vs nis is) =
    MkUseful (inhabAt c ◂ vs) (contraposition (default-preserves-≼ h) nis) (—≼ ◂ is)
  {-# COMPILE AGDA2HS usefulWildMissCase #-}

  -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
  usefulWildMissCaseInv : Useful P (— ◂ ps) → Useful (default_ P) ps
  usefulWildMissCaseInv (MkUseful (v ◂ vs) nis (i ◂ is)) =
    MkUseful vs (contraposition default-preserves-≼⁻ nis) is

--------------------------------------------------------------------------------

instance iUsefulnessUseful : Usefulness Useful
iUsefulnessUseful .nilOkCase       = usefulNilOkCase
iUsefulnessUseful .nilBadCase      = usefulNilBadCase
iUsefulnessUseful .orCase          = usefulOrCase
iUsefulnessUseful .orCaseInv       = usefulOrCaseInv
iUsefulnessUseful .conCase         = usefulConCase
iUsefulnessUseful .conCaseInv      = usefulConCaseInv
iUsefulnessUseful .wildMissCase    = usefulWildMissCase
iUsefulnessUseful .wildMissCaseInv = λ _ → usefulWildMissCaseInv
iUsefulnessUseful .wildCompCase    = λ _ → usefulWildCompCase
iUsefulnessUseful .wildCompCaseInv = λ _ → usefulWildCompCaseInv
{-# COMPILE AGDA2HS iUsefulnessUseful #-}
