open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm

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
    α β : Type
    αs βs : Types
    d : NameData
    @0 α0 β0 : Type
    @0 αs0 βs0 : Types
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Usefulness

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
record Useful ⦃ @0 sig : Signature ⦄ (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) : Set where
  constructor MkUseful
  field
    witness       : Values αs0
    @0 P⋠witness  : P ⋠** witness
    @0 ps≼witness : ps ≼* witness
open Useful public
{-# COMPILE AGDA2HS Useful newtype #-}

--------------------------------------------------------------------------------
-- Properties of ≼ and specialize/default

module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {us : Values αs} {vs : Values βs}
  where

  specializeAux-preserves-≼ : {ps : Patterns (TyData d ◂ βs)}
    → ps ≼* con c us ◂ vs
    → specializeAux c ps ≼** (us ◂◂ᵛ vs)
  specializeAux-preserves-≼ {—         ◂ ps} is = here (wildHeadLemmaInv is)
  specializeAux-preserves-≼ {con c' rs ◂ ps} is = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c')) → specializeAuxConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
      lem (False ⟨ c≢c' ⟩) = contradiction (sym (c≼c'⇒c≡c' (iUncons is .fst))) c≢c'
      lem (True ⟨ refl ⟩)  = here (conHeadLemmaInv is)
  specializeAux-preserves-≼ {r₁ ∣ r₂   ◂ ps} =
    either
      (++Any⁺ˡ ∘ specializeAux-preserves-≼)
      (++Any⁺ʳ ∘ specializeAux-preserves-≼)
    ∘ orHeadLemmaInv

  -- specialize preserves ≼
  specialize-preserves-≼ : {P : PatternMatrix (TyData d ◂ βs)}
    → P ≼** con c us ◂ vs
    → specialize c P ≼** (us ◂◂ᵛ vs)
  specialize-preserves-≼ = concatAny⁺ ∘ gmapAny⁺ specializeAux-preserves-≼

  specializeAux-preserves-≼⁻ : {ps : Patterns (TyData d ◂ βs)}
    → specializeAux c ps ≼** (us ◂◂ᵛ vs)
    → ps ≼* con c us ◂ vs
  specializeAux-preserves-≼⁻ {—         ◂ ps} (here is) = wildHeadLemma is
  specializeAux-preserves-≼⁻ {con c' rs ◂ ps} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → specializeAuxConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
        → con c' rs ◂ ps ≼* con c us ◂ vs
      lem (True ⟨ refl ⟩) (here h) = conHeadLemma h
  specializeAux-preserves-≼⁻ {r₁ ∣ r₂   ◂ ps} =
    orHeadLemma
    ∘ mapEither specializeAux-preserves-≼⁻ specializeAux-preserves-≼⁻
    ∘ ++Any⁻ _

  -- Unspecialisation preserves ≼
  specialize-preserves-≼⁻ : {P : PatternMatrix (TyData d ◂ βs)}
    → specialize c P ≼** (us ◂◂ᵛ vs)
    → P ≼** con c us ◂ vs
  specialize-preserves-≼⁻ = gmapAny⁻ specializeAux-preserves-≼⁻ ∘ concatAny⁻ _


module @0 _ ⦃ @0 sig : Signature ⦄ {c : NameCon d} {us : Values (argsTy (dataDefs sig d) c)} {vs : Values βs} where

  defaultAux-preserves-≼ : {ps : Patterns (TyData d ◂ βs)}
    → c ∉ headPattern ps
    → ps ≼* con c us ◂ vs
    → defaultAux ps ≼** vs
  defaultAux-preserves-≼ {—         ◂ ps} _ is = here (iUncons is .snd)
  defaultAux-preserves-≼ {con c' rs ◂ ps} h is = contradiction (sym (c≼c'⇒c≡c' (iUncons is .fst))) h
  defaultAux-preserves-≼ {r₁ ∣ r₂   ◂ ps} h =
    either
      (++Any⁺ˡ ∘ defaultAux-preserves-≼ (h ∘ Left))
      (++Any⁺ʳ ∘ defaultAux-preserves-≼ (h ∘ Right))
    ∘ orHeadLemmaInv

  -- If c does not appear in the first column of P, default preserves ≼
  default-preserves-≼ : {P : PatternMatrix (TyData d ◂ βs)}
    → All (λ ps → c ∉ headPattern ps) P
    → P ≼** con c us ◂ vs
    → default' P ≼** vs
  default-preserves-≼ {ps ◂ P} (h ◂ _) (here is)  =
    ++Any⁺ˡ (defaultAux-preserves-≼ h is)
  default-preserves-≼ {ps ◂ P} (_ ◂ h) (there is) =
    ++Any⁺ʳ (default-preserves-≼ h is)


module @0 _ ⦃ @0 sig : Signature ⦄ {v : Value (TyData d)} {vs : Values αs} where

  defaultAux-preserves-≼⁻ : {ps : Patterns (TyData d ◂ αs)}
    → defaultAux ps ≼** vs
    → ps ≼* v ◂ vs
  defaultAux-preserves-≼⁻ {— ◂ ps}       (here is) = —≼ ◂ is
  defaultAux-preserves-≼⁻ {r₁ ∣ r₂ ◂ ps} =
    orHeadLemma
    ∘ mapEither defaultAux-preserves-≼⁻ defaultAux-preserves-≼⁻
    ∘ ++Any⁻ _

  default-preserves-≼⁻ : {P : PatternMatrix (TyData d ◂ αs)}
    → default' P ≼** vs
    → P ≼** v ◂ vs
  default-preserves-≼⁻ = gmapAny⁻ defaultAux-preserves-≼⁻ ∘ concatAny⁻ _

--------------------------------------------------------------------------------
-- Properties of usefulness

module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  inhabAt : (c : NameCon d) → Value (TyData d)
  inhabAt c = con c (tabulateValues λ α → nonEmptyAxiom)
  {-# COMPILE AGDA2HS inhabAt inline #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- ⌈⌉ is useful wrt []
  usefulVNilNil : Useful [] ⌈⌉
  usefulVNilNil = MkUseful ⌈⌉ (λ ()) ⌈⌉
  {-# COMPILE AGDA2HS usefulVNilNil #-}

  -- [] is not wrt any non-empty matrix
  usefulVConsNil : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ Useful (ps ∷ P) ⌈⌉
  usefulVConsNil {⌈⌉} (MkUseful ⌈⌉ h _) = contradiction (here ⌈⌉) h

module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulVOrHead : Either (Useful P (r₁ ◂ ps)) (Useful P (r₂ ◂ ps)) → Useful P (r₁ ∣ r₂ ◂ ps)
  usefulVOrHead (Left (MkUseful (v ◂ vs) nis (i ◂ is))) =
    MkUseful (v ◂ vs) nis (∣≼ˡ i ◂ is)
  usefulVOrHead (Right (MkUseful (v ◂ vs) nis (i ◂ is))) =
    MkUseful (v ◂ vs) nis (∣≼ʳ i ◂ is)
  {-# COMPILE AGDA2HS usefulVOrHead #-}

  @0 usefulVOrHeadInv : Useful P (r₁ ∣ r₂ ◂ ps) → Either (Useful P (r₁ ◂ ps)) (Useful P (r₂ ◂ ps))
  usefulVOrHeadInv (MkUseful vs nis (∣≼ˡ i ◂ is)) = Left (MkUseful vs nis (i ◂ is))
  usefulVOrHeadInv (MkUseful vs nis (∣≼ʳ i ◂ is)) = Right (MkUseful vs nis (i ◂ is))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {c : NameCon d} {@0 rs : Patterns (argsTy (dataDefs sig d) c)} {@0 ps : Patterns αs0} where

  usefulVConHead : Useful (specialize c P) (rs ◂◂ᵖ ps) → Useful P (con c rs ◂ ps)
  usefulVConHead (MkUseful usvs nis is) = case splitInstances rs is of λ where
    ((us , vs) ⟨ refl , (is1 , is2) ⟩) →
      MkUseful (con c us ◂ vs) (contraposition specialize-preserves-≼ nis) (con≼ is1 ◂ is2)
  {-# COMPILE AGDA2HS usefulVConHead #-}


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulVConHeadInv : Useful P (con c rs ◂ ps) → Useful (specialize c P) (rs ◂◂ᵖ ps)
  usefulVConHeadInv (MkUseful (con c vs ◂ us) nis (con≼ is ◂ is')) =
    MkUseful (vs ◂◂ᵛ us) (contraposition specialize-preserves-≼⁻ nis) (is ◂◂ⁱ is')


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`, `∙ ∷ ps` is also useful wrt P
  usefulVWildHeadComp :
      Σ[ c ∈ NameCon d ] Useful (specialize c P) (—* ◂◂ᵖ ps)
    → Useful P (— ◂ ps)
  usefulVWildHeadComp (c , MkUseful usvs nis is) =
    case splitInstances {αs = argsTy (dataDefs sig d) c} —* is of λ where
      ((us , vs) ⟨ refl , (_ , is') ⟩) →
        MkUseful (con c us ◂ vs) (contraposition specialize-preserves-≼ nis) (—≼ ◂ is')
  {-# COMPILE AGDA2HS usefulVWildHeadComp #-}

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`
  usefulVWildHeadCompInv :
      Useful P (— ◂ ps)
    → Σ[ c ∈ NameCon d ] Useful (specialize c P) (—* ◂◂ᵖ ps)
  usefulVWildHeadCompInv (MkUseful (con c us ◂ vs) nis (_ ◂ is)) =
    c , MkUseful (us ◂◂ᵛ vs) (contraposition specialize-preserves-≼⁻ nis) (—≼* ◂◂ⁱ is)


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
  usefulVWildHeadMiss :
      ∃[ c ∈ NameCon d ] All (λ ps → c ∉ headPattern ps) P
    → Useful (default' P) ps → Useful P (— ◂ ps)
  usefulVWildHeadMiss (c ⟨ h ⟩) (MkUseful vs nis is) =
    MkUseful (inhabAt c ◂ vs) (contraposition (default-preserves-≼ h) nis) (—≼ ◂ is)
  {-# COMPILE AGDA2HS usefulVWildHeadMiss #-}

  -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
  usefulVWildHeadMissInv : Useful P (— ◂ ps) → Useful (default' P) ps
  usefulVWildHeadMissInv (MkUseful (v ◂ vs) nis (i ◂ is)) =
    MkUseful vs (contraposition default-preserves-≼⁻ nis) is

--------------------------------------------------------------------------------

instance iUsefulnessUseful : Usefulness Useful
iUsefulnessUseful .nilNil          = usefulVNilNil
iUsefulnessUseful .consNil         = usefulVConsNil
iUsefulnessUseful .orHead          = usefulVOrHead
iUsefulnessUseful .orHeadInv       = usefulVOrHeadInv
iUsefulnessUseful .conHead         = usefulVConHead
iUsefulnessUseful .conHeadInv      = usefulVConHeadInv
iUsefulnessUseful .wildHeadMiss    = usefulVWildHeadMiss
iUsefulnessUseful .wildHeadMissInv = λ _ → usefulVWildHeadMissInv
iUsefulnessUseful .wildHeadComp    = λ _ → usefulVWildHeadComp
iUsefulnessUseful .wildHeadCompInv = λ _ → usefulVWildHeadCompInv
{-# COMPILE AGDA2HS iUsefulnessUseful #-}
