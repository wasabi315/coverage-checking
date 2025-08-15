open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm

module CoverageCheck.Usefulness.UsefulV
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
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

module _ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  inhabAtArgs : ⦃ sig' : Rezz sig ⦄ (c : NameCon d) → Values (argsTy (dataDefs sig d) c)
  inhabAtArgs ⦃ rezz sig' ⦄ c = tabulateValues ⦃ sig = sig' ⦄ λ α → nonEmptyAxiom
  {-# COMPILE AGDA2HS inhabAtArgs #-}

  inhabAt : ⦃ sig' : Rezz sig ⦄ (c : NameCon d) → Value (TyData d)
  inhabAt c = con c (inhabAtArgs c)
  {-# COMPILE AGDA2HS inhabAt inline #-}

--------------------------------------------------------------------------------
-- Usefulness

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
record UsefulV (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) : Set where
  constructor MkUsefulV
  field
    witness       : Values αs0
    @0 P⋠witness  : P ⋠** witness
    @0 witness≼ps : ps ≼* witness
open UsefulV public
{-# COMPILE AGDA2HS UsefulV newtype #-}

--------------------------------------------------------------------------------
-- Properties of ≼ and specialise/default

module @0 _ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {us : Values αs} {vs : Values βs}
  where

  specialiseAux-preserves-≼ : {ps : Patterns (TyData d ◂ βs)}
    → ps ≼* con c us ◂ vs
    → specialiseAux c ps ≼** (us ◂◂ᵛ vs)
  specialiseAux-preserves-≼ {—         ◂ ps} is = here (wildHeadLemmaInv is)
  specialiseAux-preserves-≼ {con c' rs ◂ ps} is = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c')) → specialiseAuxConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
      lem (False ⟨ c≢c' ⟩) = contradiction (sym (c≼c'⇒c≡c' (iUncons is .fst))) c≢c'
      lem (True ⟨ refl ⟩)  = here (conHeadLemmaInv is)
  specialiseAux-preserves-≼ {r₁ ∣ r₂   ◂ ps} =
    either
      (++Any⁺ˡ ∘ specialiseAux-preserves-≼)
      (++Any⁺ʳ ∘ specialiseAux-preserves-≼)
    ∘ orHeadLemmaInv

  -- specialise preserves ≼
  specialise-preserves-≼ : {P : PatternMatrix (TyData d ◂ βs)}
    → P ≼** con c us ◂ vs
    → specialise c P ≼** (us ◂◂ᵛ vs)
  specialise-preserves-≼ = concatAny⁺ ∘ gmapAny⁺ specialiseAux-preserves-≼

  specialiseAux-preserves-≼⁻ : {ps : Patterns (TyData d ◂ βs)}
    → specialiseAux c ps ≼** (us ◂◂ᵛ vs)
    → ps ≼* con c us ◂ vs
  specialiseAux-preserves-≼⁻ {—         ◂ ps} (here is) = wildHeadLemma is
  specialiseAux-preserves-≼⁻ {con c' rs ◂ ps} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → specialiseAuxConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
        → con c' rs ◂ ps ≼* con c us ◂ vs
      lem (True ⟨ refl ⟩) (here h) = conHeadLemma h
  specialiseAux-preserves-≼⁻ {r₁ ∣ r₂   ◂ ps} =
    orHeadLemma
    ∘ mapEither specialiseAux-preserves-≼⁻ specialiseAux-preserves-≼⁻
    ∘ ++Any⁻ _

  -- Unspecialisation preserves ≼
  specialise-preserves-≼⁻ : {P : PatternMatrix (TyData d ◂ βs)}
    → specialise c P ≼** (us ◂◂ᵛ vs)
    → P ≼** con c us ◂ vs
  specialise-preserves-≼⁻ = gmapAny⁻ specialiseAux-preserves-≼⁻ ∘ concatAny⁻ _


module @0 _ {c : NameCon d} {us : Values (argsTy (dataDefs sig d) c)} {vs : Values βs} where

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


module @0 _ {v : Value (TyData d)} {vs : Values αs} where

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

-- ⌈⌉ is useful wrt []
usefulVNilNil : UsefulV [] ⌈⌉
usefulVNilNil = MkUsefulV ⌈⌉ (λ ()) ⌈⌉
{-# COMPILE AGDA2HS usefulVNilNil #-}

-- [] is not wrt any non-empty matrix
usefulVConsNil : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ UsefulV (ps ∷ P) ⌈⌉
usefulVConsNil {⌈⌉} (MkUsefulV ⌈⌉ h _) = contradiction (here ⌈⌉) h

module _ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulVOrHead : Either (UsefulV P (r₁ ◂ ps)) (UsefulV P (r₂ ◂ ps)) → UsefulV P (r₁ ∣ r₂ ◂ ps)
  usefulVOrHead (Left (MkUsefulV (v ◂ vs) nis (i ◂ is))) =
    MkUsefulV (v ◂ vs) nis (∣≼ˡ i ◂ is)
  usefulVOrHead (Right (MkUsefulV (v ◂ vs) nis (i ◂ is))) =
    MkUsefulV (v ◂ vs) nis (∣≼ʳ i ◂ is)
  {-# COMPILE AGDA2HS usefulVOrHead #-}

  @0 usefulVOrHeadInv : UsefulV P (r₁ ∣ r₂ ◂ ps) → Either (UsefulV P (r₁ ◂ ps)) (UsefulV P (r₂ ◂ ps))
  usefulVOrHeadInv (MkUsefulV vs nis (∣≼ˡ i ◂ is)) = Left (MkUsefulV vs nis (i ◂ is))
  usefulVOrHeadInv (MkUsefulV vs nis (∣≼ʳ i ◂ is)) = Right (MkUsefulV vs nis (i ◂ is))


module _ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {c : NameCon d0} {rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulVConHead : UsefulV (specialise c P) (rs ◂◂ᵖ ps) → UsefulV P (con c rs ◂ ps)
  usefulVConHead (MkUsefulV usvs nis is) = case splitInstances rs is of λ where
    ((us , vs) ⟨ refl , (is1 , is2) ⟩) →
      MkUsefulV (con c us ◂ vs) (contraposition specialise-preserves-≼ nis) (con≼ is1 ◂ is2)
  {-# COMPILE AGDA2HS usefulVConHead #-}


module _ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulVConHeadInv : UsefulV P (con c rs ◂ ps) → UsefulV (specialise c P) (rs ◂◂ᵖ ps)
  usefulVConHeadInv (MkUsefulV (con c vs ◂ us) nis (con≼ is ◂ is')) =
    MkUsefulV (vs ◂◂ᵛ us) (contraposition specialise-preserves-≼⁻ nis) (is ◂◂ⁱ is')


module _ {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ sig' : Rezz sig ⦄
  where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialise c P`, `∙ ∷ ps` is also useful wrt P
  usefulVWildHeadComp :
      Σ[ c ∈ NameCon d ] UsefulV (specialise c P) (—* ◂◂ᵖ ps)
    → UsefulV P (— ◂ ps)
  usefulVWildHeadComp (c , MkUsefulV usvs nis is) =
    case sig' of λ where
      (rezz sig) → let instance _ = sig in
        case splitInstances (—* {αs = argsTy (dataDefs sig d) c}) is of λ where
        ((us , vs) ⟨ refl , (_ , is') ⟩) →
          MkUsefulV (con c us ◂ vs) (contraposition specialise-preserves-≼ nis) (—≼ ◂ is')
  {-# COMPILE AGDA2HS usefulVWildHeadComp #-}

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialise c P`
  usefulVWildHeadCompInv :
      UsefulV P (— ◂ ps)
    → Σ[ c ∈ NameCon d ] UsefulV (specialise c P) (—* ◂◂ᵖ ps)
  usefulVWildHeadCompInv (MkUsefulV (con c us ◂ vs) nis (_ ◂ is)) =
    c , MkUsefulV (us ◂◂ᵛ vs) (contraposition specialise-preserves-≼⁻ nis) (—≼* ◂◂ⁱ is)


module _ {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ sig' : Rezz sig ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
  usefulVWildHeadMiss : ∃[ c ∈ NameCon d ] All (λ ps → c ∉ headPattern ps) P
    → UsefulV (default' P) ps → UsefulV P (— ◂ ps)
  usefulVWildHeadMiss (c ⟨ h ⟩) (MkUsefulV vs nis is) =
    MkUsefulV (inhabAt c ◂ vs) (contraposition (default-preserves-≼ h) nis) (—≼ ◂ is)
  {-# COMPILE AGDA2HS usefulVWildHeadMiss #-}

  -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
  usefulVWildHeadMissInv : UsefulV P (— ◂ ps) → UsefulV (default' P) ps
  usefulVWildHeadMissInv (MkUsefulV (v ◂ vs) nis (i ◂ is)) =
    MkUsefulV vs (contraposition default-preserves-≼⁻ nis) is

--------------------------------------------------------------------------------

instance iUsefulnessUsefulV : Usefulness UsefulV
iUsefulnessUsefulV .nilNil          = usefulVNilNil
iUsefulnessUsefulV .consNil         = usefulVConsNil
iUsefulnessUsefulV .orHead          = usefulVOrHead
iUsefulnessUsefulV .orHeadInv       = usefulVOrHeadInv
iUsefulnessUsefulV .conHead         = usefulVConHead
iUsefulnessUsefulV .conHeadInv      = usefulVConHeadInv
iUsefulnessUsefulV .wildHeadMiss    = usefulVWildHeadMiss
iUsefulnessUsefulV .wildHeadMissInv = λ _ → usefulVWildHeadMissInv
iUsefulnessUsefulV .wildHeadComp    = λ _ → usefulVWildHeadComp
iUsefulnessUsefulV .wildHeadCompInv = λ _ → usefulVWildHeadCompInv
{-# COMPILE AGDA2HS iUsefulnessUsefulV #-}
