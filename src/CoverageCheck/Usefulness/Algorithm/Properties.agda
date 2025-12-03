open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

open import CoverageCheck.Usefulness.Algorithm.Types
open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors

module @0 CoverageCheck.Usefulness.Algorithm.Properties
  ⦃ globals : Globals ⦄
  ⦃ sig : Signature ⦄
  where

private open module G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    αss : TyStack
    d : NameData

--------------------------------------------------------------------------------
-- Properties of ≼ and specialize/default

module _ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {us : Values αs} {vs : Values βs} {vss : ValueStack αss}
  where

  -- specialize preserves ≼

  specialize'-preserves-≼ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → pss ≼ˢ (con c us ∷ vs) ∷ vss
    → specialize' c pss ≼ˢᵐ us ∷ vs ∷ vss
  specialize'-preserves-≼ {(— ∷ ps) ∷ pss} ((_ ∷ insts) ∷ instss) =
    here (—*≼ ∷ insts ∷ instss)
  specialize'-preserves-≼ {(con c' rs ∷ ps) ∷ pss} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → ((con c' rs ∷ ps) ∷ pss) ≼ˢ ((con c us ∷ vs) ∷ vss)
        → specializeConCase c rs ps pss eq ≼ˢᵐ us ∷ vs ∷ vss
      lem (False ⟨ c≢c' ⟩) ((inst ∷ _) ∷ _) =
        contradiction (sym (c≼c'⇒c≡c' inst)) c≢c'
      lem (True ⟨ refl ⟩) ((con≼ insts' ∷ insts) ∷ instss) =
        here (insts' ∷ insts ∷ instss)
  specialize'-preserves-≼ {(r₁ ∣ r₂ ∷ ps) ∷ pss} ((∣≼ˡ inst ∷ insts) ∷ instss) =
    ++Any⁺ˡ (specialize'-preserves-≼ ((inst ∷ insts) ∷ instss))
  specialize'-preserves-≼ {(r₁ ∣ r₂ ∷ ps) ∷ pss} ((∣≼ʳ inst ∷ insts) ∷ instss) =
    ++Any⁺ʳ (specialize'-preserves-≼ ((inst ∷ insts) ∷ instss))

  specialize-preserves-≼ : {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
    → psmat ≼ˢᵐ ((con c us ∷ vs) ∷ vss)
    → specialize c psmat ≼ˢᵐ (us ∷ vs ∷ vss)
  specialize-preserves-≼ = gconcatMapAny⁺ specialize'-preserves-≼

  -- Unspecialization also preserves ≼

  specialize'-preserves-≼⁻ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → specialize' c pss ≼ˢᵐ (us ∷ vs ∷ vss)
    → pss ≼ˢ ((con c us ∷ vs) ∷ vss)
  specialize'-preserves-≼⁻ {(— ∷ ps) ∷ pss} (here (_ ∷ insts ∷ instss)) =
    (—≼ ∷ insts) ∷ instss
  specialize'-preserves-≼⁻ {(con c' rs ∷ ps) ∷ pss} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → specializeConCase c rs ps pss eq ≼ˢᵐ (us ∷ vs ∷ vss)
        → (con c' rs ∷ ps) ∷ pss ≼ˢ ((con c us ∷ vs) ∷ vss)
      lem (True ⟨ refl ⟩) (here (insts' ∷ insts ∷ instss)) =
        (con≼ insts' ∷ insts) ∷ instss
  specialize'-preserves-≼⁻ {(r₁ ∣ r₂ ∷ ps) ∷ pss} =
    either
      (λ where ((inst ∷ insts) ∷ instss) → (∣≼ˡ inst ∷ insts) ∷ instss)
      (λ where ((inst ∷ insts) ∷ instss) → (∣≼ʳ inst ∷ insts) ∷ instss)
    ∘ bimap
        (specialize'-preserves-≼⁻ {pss = (r₁ ∷ ps) ∷ pss})
        (specialize'-preserves-≼⁻ {pss = (r₂ ∷ ps) ∷ pss})
    ∘ ++Any⁻ _

  specialize-preserves-≼⁻ : {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
    → specialize c psmat ≼ˢᵐ (us ∷ vs ∷ vss)
    → psmat ≼ˢᵐ ((con c us ∷ vs) ∷ vss)
  specialize-preserves-≼⁻ = gconcatMapAny⁻ specialize'-preserves-≼⁻


module _ {c : NameCon d}
  {us : Values (argsTy (dataDefs sig d) c)} {vs : Values βs} {vss : ValueStack αss}
  where

  default'-preserves-≼ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → c ∉ˢ pss
    → pss ≼ˢ (con c us ∷ vs) ∷ vss
    → default' pss ≼ˢᵐ vs ∷ vss
  default'-preserves-≼ {(— ∷ ps) ∷ pss} h ((_ ∷ insts) ∷ instss) =
    here (insts ∷ instss)
  default'-preserves-≼ {(con c' rs ∷ ps) ∷ pss} h ((inst ∷ _) ∷ _) =
    contradiction (sym (c≼c'⇒c≡c' inst)) h
  default'-preserves-≼ {(p ∣ q ∷ ps) ∷ pss} h ((∣≼ˡ inst ∷ insts) ∷ instss) =
    ++Any⁺ˡ (default'-preserves-≼ (h ∘ Left) ((inst ∷ insts) ∷ instss))
  default'-preserves-≼ {(p ∣ q ∷ ps) ∷ pss} h ((∣≼ʳ inst ∷ insts) ∷ instss) =
    ++Any⁺ʳ (default'-preserves-≼ (h ∘ Right) ((inst ∷ insts) ∷ instss))

  -- If c does not appear in the first column of psmat, default preserves ≼
  default-preserves-≼ : {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
    → c ∉ˢᵐ psmat
    → psmat ≼ˢᵐ (con c us ∷ vs) ∷ vss
    → default_ psmat ≼ˢᵐ vs ∷ vss
  default-preserves-≼ {pss ∷ psmat} (h ∷ _) (here instss) =
    ++Any⁺ˡ (default'-preserves-≼ h instss)
  default-preserves-≼ {pss ∷ psmat} (_ ∷ h) (there instsMat) =
    ++Any⁺ʳ (default-preserves-≼ h instsMat)


module _ {v : Value (TyData d)} {vs : Values αs} {vss : ValueStack αss} where

  default'-preserves-≼⁻ : {pss : PatternStack ((TyData d ∷ αs) ∷ αss)}
    → default' pss ≼ˢᵐ vs ∷ vss
    → pss ≼ˢ (v ∷ vs) ∷ vss
  default'-preserves-≼⁻ {(— ∷ ps) ∷ pss} (here (insts ∷ instss)) =
    (—≼ ∷ insts) ∷ instss
  default'-preserves-≼⁻ {(r₁ ∣ r₂ ∷ ps) ∷ pss} =
    either
      (λ where ((inst ∷ insts) ∷ instss) → (∣≼ˡ inst ∷ insts) ∷ instss)
      (λ where ((inst ∷ insts) ∷ instss) → (∣≼ʳ inst ∷ insts) ∷ instss)
    ∘ bimap
        (default'-preserves-≼⁻ {pss = (r₁ ∷ ps) ∷ pss})
        (default'-preserves-≼⁻ {pss = (r₂ ∷ ps) ∷ pss})
    ∘ ++Any⁻ _

  default-preserves-≼⁻ : {psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss)}
    → default_ psmat ≼ˢᵐ vs ∷ vss
    → psmat ≼ˢᵐ (v ∷ vs) ∷ vss
  default-preserves-≼⁻ = gconcatMapAny⁻ default'-preserves-≼⁻

--------------------------------------------------------------------------------
-- Properties of disjointness

module _ {psmat : PatternStackMatrix ([] ∷ αss)} {pss : PatternStack αss} where

  #-tail : psmat #ˢᵐ ([] ∷ pss) → map tailAll psmat #ˢᵐ pss
  #-tail disj instsMat instss =
    disj
      (gmapAny⁻ (λ where {[] ∷ _} instss' → [] ∷ instss') instsMat)
      ([] ∷ instss)

  #-tail⁻ : map tailAll psmat #ˢᵐ pss → psmat #ˢᵐ ([] ∷ pss)
  #-tail⁻ disj instsMat ([] ∷ instss) =
    disj (gmapAny⁺ (λ where {[] ∷ _} ([] ∷ instss') → instss') instsMat) instss


module _
  {psmat : PatternStackMatrix ((α ∷ αs) ∷ αss)}
  {p q : Pattern α} {ps : Patterns αs} {pss : PatternStack αss}
  where

  #-∣ˡ : psmat #ˢᵐ ((p ∣ q ∷ ps) ∷ pss) → psmat #ˢᵐ ((p ∷ ps) ∷ pss)
  #-∣ˡ disj instsMat ((inst ∷ insts) ∷ instss) =
    disj instsMat ((∣≼ˡ inst ∷ insts) ∷ instss)

  #-∣ʳ : psmat #ˢᵐ ((p ∣ q ∷ ps) ∷ pss) → psmat #ˢᵐ ((q ∷ ps) ∷ pss)
  #-∣ʳ disj instsMat ((inst ∷ insts) ∷ instss) =
    disj instsMat ((∣≼ʳ inst ∷ insts) ∷ instss)


module _ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
  {rs₁ : Patterns αs} {rs₂ : Patterns βs} {pss : PatternStack αss}
  where

  specialize-preserves-#
    : psmat #ˢᵐ ((con c rs₁ ∷ rs₂) ∷ pss)
    → specialize c psmat #ˢᵐ (rs₁ ∷ rs₂ ∷ pss)
  specialize-preserves-# disj instsMat (insts ∷ insts' ∷ instss) =
    disj (specialize-preserves-≼⁻ instsMat) ((con≼ insts ∷ insts') ∷ instss)

  specialize-preserves-#⁻
    : specialize c psmat #ˢᵐ (rs₁ ∷ rs₂ ∷ pss)
    → psmat #ˢᵐ ((con c rs₁ ∷ rs₂) ∷ pss)
  specialize-preserves-#⁻ disj instsMat ((con≼ insts ∷ insts') ∷ instss) =
    disj (specialize-preserves-≼ instsMat) (insts ∷ insts' ∷ instss)


module _ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
  {rs : Patterns βs} {pss : PatternStack αss}
  where

  specialize-preserves-#-wild
    : psmat #ˢᵐ ((— ∷ rs) ∷ pss)
    → specialize c psmat #ˢᵐ (—* ∷ rs ∷ pss)
  specialize-preserves-#-wild disj instsMat (_ ∷ insts ∷ instss) =
    disj (specialize-preserves-≼⁻ instsMat) ((—≼ ∷ insts) ∷ instss)


module _ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss)}
  {p : Pattern (TyData d)} {ps : Patterns αs} {pss : PatternStack αss}
  where

  default-preserves-#
    : psmat #ˢᵐ ((p ∷ ps) ∷ pss)
    → default_ psmat #ˢᵐ (ps ∷ pss)
  default-preserves-# disj instsMat (insts ∷ instss) =
    disj (default-preserves-≼⁻ instsMat) ((exampleFor≼ _ ∷ insts) ∷ instss)


module _ {c : NameCon d}
  {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
  {qs : Patterns (argsTy (dataDefs sig d) c)}
  {rs : Patterns βs} {pss : PatternStack αss}
  where

  default-preserves-#⁻
    : c ∉ˢᵐ psmat
    → default_ psmat #ˢᵐ (rs ∷ pss)
    → psmat #ˢᵐ ((con c qs ∷ rs) ∷ pss)
  default-preserves-#⁻ h disj instsMat ((con≼ _ ∷ insts) ∷ instss) =
    disj (default-preserves-≼ h instsMat) (insts ∷ instss)


module _
  {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)}
  {qs : Patterns βs} {pss : PatternStack αss}
  where

  default-preserves-#⁻-wild
    : (∀ c → c ∉ˢᵐ psmat)
    → default_ psmat #ˢᵐ (qs ∷ pss)
    → psmat #ˢᵐ ((— ∷ qs) ∷ pss)
  default-preserves-#⁻-wild h disj {(con c us ∷ _) ∷ _} instsMat ((—≼ ∷ insts) ∷ instss) =
    disj (default-preserves-≼ (h _) instsMat) (insts ∷ instss)
