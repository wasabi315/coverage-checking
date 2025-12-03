open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

open import CoverageCheck.Usefulness.Algorithm.Types
open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors

module CoverageCheck.Usefulness.Algorithm.Properties
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    αs βs : Tys
    αss : TyStack
    d : NameData
    @0 α0 : Ty
    @0 αs0 : Tys
    @0 αss0 : TyStack

--------------------------------------------------------------------------------
-- Properties of ≼ and specialize/default

module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {us : Values αs} {vs : Values βs} {vss : ValueStack αss}
  where

  specialize'-preserves-≼ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → pss ≼*ˢ (con c us ∷ vs) ∷ vss
    → specialize' c pss ≼**ˢ us ∷ vs ∷ vss
  specialize'-preserves-≼ {(— ∷ ps) ∷ pss} ((i ∷ is) ∷ iss) =
    here (—≼* ∷ is ∷ iss)
  specialize'-preserves-≼ {(con c' rs ∷ ps) ∷ pss} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → ((con c' rs ∷ ps) ∷ pss) ≼*ˢ ((con c us ∷ vs) ∷ vss)
        → specializeConCase c rs ps pss eq ≼**ˢ us ∷ vs ∷ vss
      lem (False ⟨ c≢c' ⟩) ((i        ∷ is) ∷ iss) = contradiction (sym (c≼c'⇒c≡c' i)) c≢c'
      lem (True  ⟨ refl ⟩) ((con≼ is' ∷ is) ∷ iss) = here (is' ∷ is ∷ iss)
  specialize'-preserves-≼ {(r₁ ∣ r₂ ∷ ps) ∷ pss} ((∣≼ˡ i ∷ is) ∷ iss) =
    ++Any⁺ˡ (specialize'-preserves-≼ ((i ∷ is) ∷ iss))
  specialize'-preserves-≼ {(r₁ ∣ r₂ ∷ ps) ∷ pss} ((∣≼ʳ i ∷ is) ∷ iss) =
    ++Any⁺ʳ (specialize'-preserves-≼ ((i ∷ is) ∷ iss))

  -- specialize preserves ≼
  specialize-preserves-≼ : {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
    → P ≼**ˢ ((con c us ∷ vs) ∷ vss)
    → specialize c P ≼**ˢ (us ∷ vs ∷ vss)
  specialize-preserves-≼ = gconcatMapAny⁺ specialize'-preserves-≼

  specialize'-preserves-≼⁻ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → specialize' c pss ≼**ˢ (us ∷ vs ∷ vss)
    → pss ≼*ˢ ((con c us ∷ vs) ∷ vss)
  specialize'-preserves-≼⁻ {(— ∷ ps) ∷ pss} (here (_ ∷ is ∷ iss)) =
    (—≼ ∷ is) ∷ iss
  specialize'-preserves-≼⁻ {(con c' rs ∷ ps) ∷ pss} = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → specializeConCase c rs ps pss eq ≼**ˢ (us ∷ vs ∷ vss)
        → (con c' rs ∷ ps) ∷ pss ≼*ˢ ((con c us ∷ vs) ∷ vss)
      lem (True ⟨ refl ⟩) (here (is' ∷ is ∷ iss)) = (con≼ is' ∷ is) ∷ iss
  specialize'-preserves-≼⁻ {(r₁ ∣ r₂ ∷ ps) ∷ pss} =
    either
      (λ where ((i ∷ is) ∷ iss) → (∣≼ˡ i ∷ is) ∷ iss)
      (λ where ((i ∷ is) ∷ iss) → (∣≼ʳ i ∷ is) ∷ iss)
    ∘ bimap
        (specialize'-preserves-≼⁻ {pss = (r₁ ∷ ps) ∷ pss})
        (specialize'-preserves-≼⁻ {pss = (r₂ ∷ ps) ∷ pss})
    ∘ ++Any⁻ _

  -- Unspecialisation preserves ≼
  specialize-preserves-≼⁻ : {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
    → specialize c P ≼**ˢ (us ∷ vs ∷ vss)
    → P ≼**ˢ ((con c us ∷ vs) ∷ vss)
  specialize-preserves-≼⁻ = gconcatMapAny⁻ specialize'-preserves-≼⁻


module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  {us : Values (argsTy (dataDefs sig d) c)} {vs : Values βs} {vss : ValueStack αss}
  where

  default'-preserves-≼ : {pss : PatternStack ((TyData d ∷ βs) ∷ αss)}
    → c ∉* pss
    → pss ≼*ˢ (con c us ∷ vs) ∷ vss
    → default' pss ≼**ˢ vs ∷ vss
  default'-preserves-≼ {(— ∷ ps) ∷ pss} h ((_ ∷ is) ∷ iss) =
    here (is ∷ iss)
  default'-preserves-≼ {(con c' rs ∷ ps) ∷ pss} h ((i ∷ is) ∷ iss) =
    contradiction (sym (c≼c'⇒c≡c' i)) h
  default'-preserves-≼ {(p ∣ p₁ ∷ ps) ∷ pss} h ((∣≼ˡ i ∷ is) ∷ iss) =
    ++Any⁺ˡ (default'-preserves-≼ (h ∘ Left) ((i ∷ is) ∷ iss))
  default'-preserves-≼ {(p ∣ p₁ ∷ ps) ∷ pss} h ((∣≼ʳ i ∷ is) ∷ iss) =
    ++Any⁺ʳ (default'-preserves-≼ (h ∘ Right) ((i ∷ is) ∷ iss))

  -- If c does not appear in the first column of P, default preserves ≼
  default-preserves-≼ : {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
    → c ∉** P
    → P ≼**ˢ (con c us ∷ vs) ∷ vss
    → default_ P ≼**ˢ vs ∷ vss
  default-preserves-≼ {ps ∷ P} (h ∷ _) (here is) =
    ++Any⁺ˡ (default'-preserves-≼ h is)
  default-preserves-≼ {ps ∷ P} (_ ∷ h) (there iss) =
    ++Any⁺ʳ (default-preserves-≼ h iss)


module @0 _ ⦃ sig : Signature ⦄ {v : Value (TyData d)} {vs : Values αs} {vss : ValueStack αss} where

  default'-preserves-≼⁻ : {pss : PatternStack ((TyData d ∷ αs) ∷ αss)}
    → default' pss ≼**ˢ vs ∷ vss
    → pss ≼*ˢ (v ∷ vs) ∷ vss
  default'-preserves-≼⁻ {(— ∷ ps) ∷ pss} (here (is ∷ iss)) =
    (—≼ ∷ is) ∷ iss
  default'-preserves-≼⁻ {(r₁ ∣ r₂ ∷ ps) ∷ pss} =
    either
      (λ where ((i ∷ is) ∷ iss) → (∣≼ˡ i ∷ is) ∷ iss)
      (λ where ((i ∷ is) ∷ iss) → (∣≼ʳ i ∷ is) ∷ iss)
    ∘ bimap
        (default'-preserves-≼⁻ {pss = (r₁ ∷ ps) ∷ pss})
        (default'-preserves-≼⁻ {pss = (r₂ ∷ ps) ∷ pss})
    ∘ ++Any⁻ _

  default-preserves-≼⁻ : {P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss)}
    → default_ P ≼**ˢ vs ∷ vss
    → P ≼**ˢ (v ∷ vs) ∷ vss
  default-preserves-≼⁻ = gconcatMapAny⁻ default'-preserves-≼⁻

--------------------------------------------------------------------------------
-- Properties of disjointness

module @0 _ ⦃ sig : Signature ⦄
  {P : PatternMatrixStack ([] ∷ αss0)} {pss : PatternStack αss0}
  where

  #**-tail : P #** ([] ∷ pss) → map tailAll P #** pss
  #**-tail disj isss iss = disj (gmapAny⁻ (λ where {[] ∷ _} iss' → [] ∷ iss') isss) ([] ∷ iss)

  #**-tail⁻ : map tailAll P #** pss → P #** ([] ∷ pss)
  #**-tail⁻ disj isss ([] ∷ iss) = disj (gmapAny⁺ (λ where {[] ∷ _} ([] ∷ iss') → iss') isss) iss


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
  {@0 p q : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  #-∣ˡ : P #** ((p ∣ q ∷ ps) ∷ pss) → P #** ((p ∷ ps) ∷ pss)
  #-∣ˡ disj isss ((i ∷ is) ∷ iss) = disj isss ((∣≼ˡ i ∷ is) ∷ iss)

  #-∣ʳ : P #** ((p ∣ q ∷ ps) ∷ pss) → P #** ((q ∷ ps) ∷ pss)
  #-∣ʳ disj isss ((i ∷ is) ∷ iss) = disj isss ((∣≼ʳ i ∷ is) ∷ iss)


module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
  {rs₁ : Patterns αs} {rs₂ : Patterns βs} {pss : PatternStack αss}
  where

  specialize-preserves-#** :
    P #** ((con c rs₁ ∷ rs₂) ∷ pss) → specialize c P #** (rs₁ ∷ rs₂ ∷ pss)
  specialize-preserves-#** disj isss (is₁ ∷ is₂ ∷ iss) =
    disj (specialize-preserves-≼⁻ isss) ((con≼ is₁ ∷ is₂) ∷ iss)

  specialize-preserves-#**⁻ :
    specialize c P #** (rs₁ ∷ rs₂ ∷ pss) → P #** ((con c rs₁ ∷ rs₂) ∷ pss)
  specialize-preserves-#**⁻ disj isss ((con≼ is₁ ∷ is₂) ∷ iss) =
    disj (specialize-preserves-≼ isss) (is₁ ∷ is₂ ∷ iss)


module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
  {rs : Patterns βs} {pss : PatternStack αss}
  where

  specialize-preserves-#**-wild :
    P #** ((— ∷ rs) ∷ pss) → specialize c P #** (—* ∷ rs ∷ pss)
  specialize-preserves-#**-wild disj isss (_ ∷ is' ∷ iss) =
    disj (specialize-preserves-≼⁻ isss) ((—≼ ∷ is') ∷ iss)


module @0 _ ⦃ @0 sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss)}
  {p : Pattern (TyData d)} {ps : Patterns αs} {pss : PatternStack αss}
  where

  default-preserves-#** : P #** ((p ∷ ps) ∷ pss) → default_ P #** (ps ∷ pss)
  default-preserves-#** disj isss (is ∷ iss) =
    disj (default-preserves-≼⁻ isss) ((exampleFor≼ _ ∷ is) ∷ iss)


module @0 _ ⦃ @0 sig : Signature ⦄ {c : NameCon d}
  {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
  {qs : Patterns (argsTy (dataDefs sig d) c)} {rs : Patterns βs} {pss : PatternStack αss}
  where

  default-preserves-#**⁻ :
      c ∉** P
    → default_ P #** (rs ∷ pss)
    → P #** ((con c qs ∷ rs) ∷ pss)
  default-preserves-#**⁻ h disj isss ((con≼ _ ∷ is₂) ∷ iss) =
    disj (default-preserves-≼ h isss) (is₂ ∷ iss)


module @0 _ ⦃ @0 sig : Signature ⦄
  {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)}
  {qs : Patterns βs} {pss : PatternStack αss}
  where

  default-preserves-#**⁻-wild :
      (∀ c → c ∉** P)
    → default_ P #** (qs ∷ pss)
    → P #** ((— ∷ qs) ∷ pss)
  default-preserves-#**⁻-wild h disj {(con c us ∷ _) ∷ _} isss ((—≼ ∷ is) ∷ iss) =
    disj (default-preserves-≼ (h _) isss) (is ∷ iss)
