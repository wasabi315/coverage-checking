open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm

module CoverageCheck.Usefulness.Properties
  ⦃ @0 globals : Globals ⦄
  where

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
-- Properties of ≼ and specialize/default

module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {us : Values αs} {vs : Values βs}
  where

  specialize'-preserves-≼ : {ps : Patterns (TyData d ◂ βs)}
    → ps ≼* con c us ◂ vs
    → specialize' c ps ≼** (us ◂◂ᵛ vs)
  specialize'-preserves-≼ {—         ◂ ps} is = here (wildHeadLemmaInv is)
  specialize'-preserves-≼ {con c' rs ◂ ps} is = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c')) → specialize'ConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
      lem (False ⟨ c≢c' ⟩) = contradiction (sym (c≼c'⇒c≡c' (iUncons is .fst))) c≢c'
      lem (True ⟨ refl ⟩)  = here (conHeadLemmaInv is)
  specialize'-preserves-≼ {r₁ ∣ r₂   ◂ ps} =
    either
      (++Any⁺ˡ ∘ specialize'-preserves-≼)
      (++Any⁺ʳ ∘ specialize'-preserves-≼)
    ∘ orHeadLemmaInv

  -- specialize preserves ≼
  specialize-preserves-≼ : {P : PatternMatrix (TyData d ◂ βs)}
    → P ≼** con c us ◂ vs
    → specialize c P ≼** (us ◂◂ᵛ vs)
  specialize-preserves-≼ = gconcatMapAny⁺ specialize'-preserves-≼

  specialize'-preserves-≼⁻ : {ps : Patterns (TyData d ◂ βs)}
    → specialize' c ps ≼** (us ◂◂ᵛ vs)
    → ps ≼* con c us ◂ vs
  specialize'-preserves-≼⁻ {—         ◂ ps} (here is) = wildHeadLemma is
  specialize'-preserves-≼⁻ {con c' rs ◂ ps} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → specialize'ConCase c rs ps eq ≼** (us ◂◂ᵛ vs)
        → con c' rs ◂ ps ≼* con c us ◂ vs
      lem (True ⟨ refl ⟩) (here h) = conHeadLemma h
  specialize'-preserves-≼⁻ {r₁ ∣ r₂   ◂ ps} =
    orHeadLemma
    ∘ mapEither specialize'-preserves-≼⁻ specialize'-preserves-≼⁻
    ∘ ++Any⁻ _

  -- Unspecialisation preserves ≼
  specialize-preserves-≼⁻ : {P : PatternMatrix (TyData d ◂ βs)}
    → specialize c P ≼** (us ◂◂ᵛ vs)
    → P ≼** con c us ◂ vs
  specialize-preserves-≼⁻ = gconcatMapAny⁻ specialize'-preserves-≼⁻


module @0 _ ⦃ @0 sig : Signature ⦄ {c : NameCon d} {us : Values (argsTy (dataDefs sig d) c)} {vs : Values βs} where

  default'-preserves-≼ : {ps : Patterns (TyData d ◂ βs)}
    → c ∉ headPattern ps
    → ps ≼* con c us ◂ vs
    → default' ps ≼** vs
  default'-preserves-≼ {—         ◂ ps} _ is = here (iUncons is .snd)
  default'-preserves-≼ {con c' rs ◂ ps} h is = contradiction (sym (c≼c'⇒c≡c' (iUncons is .fst))) h
  default'-preserves-≼ {r₁ ∣ r₂   ◂ ps} h =
    either
      (++Any⁺ˡ ∘ default'-preserves-≼ (h ∘ Left))
      (++Any⁺ʳ ∘ default'-preserves-≼ (h ∘ Right))
    ∘ orHeadLemmaInv

  -- If c does not appear in the first column of P, default preserves ≼
  default-preserves-≼ : {P : PatternMatrix (TyData d ◂ βs)}
    → c ∉** P
    → P ≼** con c us ◂ vs
    → default_ P ≼** vs
  default-preserves-≼ {ps ◂ P} (h ◂ _) (here is)  =
    ++Any⁺ˡ (default'-preserves-≼ h is)
  default-preserves-≼ {ps ◂ P} (_ ◂ h) (there is) =
    ++Any⁺ʳ (default-preserves-≼ h is)


module @0 _ ⦃ @0 sig : Signature ⦄ {v : Value (TyData d)} {vs : Values αs} where

  default'-preserves-≼⁻ : {ps : Patterns (TyData d ◂ αs)}
    → default' ps ≼** vs
    → ps ≼* v ◂ vs
  default'-preserves-≼⁻ {— ◂ ps}       (here is) = —≼ ◂ is
  default'-preserves-≼⁻ {r₁ ∣ r₂ ◂ ps} =
    orHeadLemma
    ∘ mapEither default'-preserves-≼⁻ default'-preserves-≼⁻
    ∘ ++Any⁻ _

  default-preserves-≼⁻ : {P : PatternMatrix (TyData d ◂ αs)}
    → default_ P ≼** vs
    → P ≼** v ◂ vs
  default-preserves-≼⁻ = gconcatMapAny⁻ default'-preserves-≼⁻
