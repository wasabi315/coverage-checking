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
-- The actual algorithm operates on doubly-nested lists of patterns
-- instead of lists of patterns.
-- This is because:
--   1. efficiency: O(1) cons/uncons instead of O(n) append/split
--   2. ease of proofs: pattern matching for decomposition instead of with-abstracting the result of a split function
--
-- The following provides type synonyms for the doubly-nested things.

TyStack : Type
TyStack = List Tys
{-# COMPILE AGDA2HS TyStack inline #-}

private
  variable
    @0 αss0 : TyStack

module _ ⦃ @0 sig : Signature ⦄ where
  infix 4 InstanceStack InstanceMatrixStack _⋠ˢ_ _⋠ˢᵐ_ SubsumptionStack
  infix -1 _,_,_

  ValueStack : @0 TyStack → Type
  ValueStack αss = All Values αss
  {-# COMPILE AGDA2HS ValueStack inline #-}

  PatternStack : @0 TyStack → Type
  PatternStack αss = All Patterns αss
  {-# COMPILE AGDA2HS PatternStack inline #-}

  PatternStackMatrix : @0 TyStack → Type
  PatternStackMatrix αss = List (PatternStack αss)
  {-# COMPILE AGDA2HS PatternStackMatrix inline #-}

  -- Instance/subsumption relations between doubly-nested things

  InstanceStack : @0 ValueStack αss0 → @0 PatternStack αss0 → Type
  syntax InstanceStack vss pss = vss ≼ˢ pss
  vss ≼ˢ pss = HPointwise (λ vs ps → vs ≼* ps) vss pss
  {-# COMPILE AGDA2HS InstanceStack inline #-}

  InstanceMatrixStack : @0 ValueStack αss0 → @0 PatternStackMatrix αss0 → Type
  syntax InstanceMatrixStack vss psss = vss ≼ˢᵐ psss
  vss ≼ˢᵐ psmat = Any (λ pss → vss ≼ˢ pss) psmat
  {-# COMPILE AGDA2HS InstanceMatrixStack inline #-}

  _⋠ˢ_ : @0 ValueStack αss0 → @0 PatternStack αss0 → Type
  vss ⋠ˢ pss = ¬ vss ≼ˢ pss

  _⋠ˢᵐ_ : @0 ValueStack αss0 → @0 PatternStackMatrix αss0 → Type
  vss ⋠ˢᵐ psmat = ¬ vss ≼ˢᵐ psmat

  _#ˢᵐ_ : @0 PatternStackMatrix αss0 → @0 PatternStack αss0 → Type
  psmat #ˢᵐ qss = ∀ {vss} → vss ≼ˢᵐ psmat → vss ≼ˢ qss → ⊥

  SubsumptionStack : @0 PatternStack αss0 → @0 PatternStack αss0 → Type
  syntax SubsumptionStack pss qss = pss ⊆ˢ qss
  pss ⊆ˢ vss = HPointwise (λ ps vs → ps ⊆* vs) pss vss
  {-# COMPILE AGDA2HS SubsumptionStack inline #-}

  -- Usefulness relation for doubly-nested things

  record UsefulS' (@0 psmat : PatternStackMatrix αss0) (@0 pss : PatternStack αss0) : Type where
    no-eta-equality
    pattern
    constructor _,_,_
    field
      witness : PatternStack αss0
      @0 psmat#witness : psmat #ˢᵐ witness
      @0 witness⊆pss : witness ⊆ˢ pss

  -- Type synonym rather than record to eliminate wrapping/unwrapping in algorithm
  UsefulS : @0 PatternStackMatrix αss0 → @0 PatternStack αss0 → Type
  UsefulS psmat pss = NonEmpty (UsefulS' psmat pss)

  {-# COMPILE AGDA2HS UsefulS' unboxed #-}
  {-# COMPILE AGDA2HS UsefulS inline #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} {@0 pmat : PatternMatrix αs0} {@0 ps : Patterns αs0}
  where

  -- Conversion between UsefulS and Useful

  UsefulS'→Useful' : UsefulS' (map (_∷ []) pmat) (ps ∷ []) → Useful' pmat ps
  UsefulS'→Useful' = λ where
    (qs ∷ [] , disj , subs ∷ []) →
      qs ,
      (λ instmat insts → disj (gmapAny⁺ (_∷ []) instmat) (insts ∷ [])) ,
      subs
  {-# COMPILE AGDA2HS UsefulS'→Useful' inline #-}

  UsefulS→Useful : UsefulS (map (_∷ []) pmat) (ps ∷ []) → Useful pmat ps
  UsefulS→Useful h = record { witnesses = fmap UsefulS'→Useful' h }
  {-# COMPILE AGDA2HS UsefulS→Useful inline #-}

  @0 Useful'→UsefulS' : Useful' pmat ps → UsefulS' (map (_∷ []) pmat) (ps ∷ [])
  Useful'→UsefulS' (qs , disj , subs) =
    qs ∷ [] ,
    (λ where
      {_ ∷ []} instsmat (insts ∷ []) →
        disj (gmapAny⁻ (λ where (insts' ∷ []) → insts') instsmat) insts) ,
    subs ∷ []

  @0 Useful→UsefulS : Useful pmat ps → UsefulS (map (_∷ []) pmat) (ps ∷ [])
  Useful→UsefulS = fmap Useful'→UsefulS' ∘ witnesses
