open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import Haskell.Data.List.NonEmpty using (NonEmpty)

open import CoverageCheck.Usefulness.Definition

module CoverageCheck.Usefulness.Algorithm.Types
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

--------------------------------------------------------------------------------

TyStack : Type
TyStack = List Tys
{-# COMPILE AGDA2HS TyStack inline #-}

private
  variable
    @0 αss0 : TyStack

module _ ⦃ @0 sig : Signature ⦄ where
  infix 4 InstanceStack InstanceMatrixStack _⋠ˢ_ _⋠ᵐˢ_ SubsumptionStack

  ValueStack : @0 TyStack → Type
  ValueStack αss = All Values αss
  {-# COMPILE AGDA2HS ValueStack inline #-}

  PatternStack : @0 TyStack → Type
  PatternStack αss = All Patterns αss
  {-# COMPILE AGDA2HS PatternStack inline #-}

  PatternMatrixStack : @0 TyStack → Type
  PatternMatrixStack αss = List (PatternStack αss)
  {-# COMPILE AGDA2HS PatternMatrixStack inline #-}

  InstanceStack : @0 PatternStack αss0 → @0 ValueStack αss0 → Type
  syntax InstanceStack pss vss = pss ≼ˢ vss
  pss ≼ˢ vss = HPointwise (λ ps vs → ps ≼* vs) pss vss
  {-# COMPILE AGDA2HS InstanceStack inline #-}

  InstanceMatrixStack : @0 PatternMatrixStack αss0 → @0 ValueStack αss0 → Type
  syntax InstanceMatrixStack psss vss = psss ≼ᵐˢ vss
  psss ≼ᵐˢ vss = Any (λ pss → pss ≼ˢ vss) psss
  {-# COMPILE AGDA2HS InstanceMatrixStack inline #-}

  _⋠ˢ_ : @0 PatternStack αss0 → @0 ValueStack αss0 → Type
  pss ⋠ˢ vss = ¬ pss ≼ˢ vss

  _⋠ᵐˢ_ : @0 PatternMatrixStack αss0 → @0 ValueStack αss0 → Type
  psss ⋠ᵐˢ vss = ¬ psss ≼ᵐˢ vss

  _#ᵐˢ_ : (@0 P : PatternMatrixStack αss0) (@0 qss : PatternStack αss0) → Type
  P #ᵐˢ qss = ∀ {vss} → P ≼ᵐˢ vss → qss ≼ˢ vss → ⊥

  SubsumptionStack : @0 PatternStack αss0 → @0 PatternStack αss0 → Type
  syntax SubsumptionStack pss vss = pss ⊆ˢ vss
  pss ⊆ˢ vss = HPointwise (λ ps vs → ps ⊆* vs) pss vss
  {-# COMPILE AGDA2HS SubsumptionStack inline #-}

  record UsefulS (@0 pmat : PatternMatrixStack αss0) (@0 ps : PatternStack αss0) : Type where
    no-eta-equality
    pattern
    constructor ⟪_,_,_⟫
    field
      witness : PatternStack αss0
      @0 pmat#witness : pmat #ᵐˢ witness
      @0 ps⊆witness : ps ⊆ˢ witness

  {-# COMPILE AGDA2HS UsefulS unboxed #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄ where

  UsefulS→Useful' : ∀ {@0 αs0} {@0 P : PatternMatrix αs0} {@0 ps : Patterns αs0}
    → UsefulS (map (_∷ []) P) (ps ∷ [])
    → Useful' P ps
  UsefulS→Useful' = λ where
    ⟪ qs ∷ [] , disj , ss ∷ [] ⟫ →
      ⟪ qs , (λ i1 i2 → disj (gmapAny⁺ (_∷ []) i1) (i2 ∷ [])) , ss ⟫
  {-# COMPILE AGDA2HS UsefulS→Useful' inline #-}

  @0 Useful'→UsefulS : ∀ {@0 αs0} {@0 P : PatternMatrix αs0} {@0 ps : Patterns αs0}
    → Useful' P ps
    → UsefulS (map (_∷ []) P) (ps ∷ [])
  Useful'→UsefulS ⟪ qs , disj , ss ⟫ =
    ⟪ qs ∷ []
    , (λ where
        {_ ∷ []} i1 (i2 ∷ []) → disj (gmapAny⁻ (λ where (i1 ∷ []) → i1) i1) i2)
    , ss ∷ [] ⟫
