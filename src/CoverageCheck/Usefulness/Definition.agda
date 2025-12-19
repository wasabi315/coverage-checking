open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

module CoverageCheck.Usefulness.Definition
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where

  record Useful' : Type where
    no-eta-equality
    pattern
    constructor ⟪_,_,_⟫
    field
      witness : Patterns αs0
      -- pmat and witness are disjoint, i.e. they have no common instances
      @0 pmat#witness : ∀ {vs} → pmat ≼ᵐ vs → witness ≼* vs → ⊥
      -- ps subsumes witness
      @0 ps⊆witness : ps ⊆* witness

  record Useful : Type where
    no-eta-equality
    pattern
    field
      witnesses : NonEmpty Useful'

  open Useful public

  {-# COMPILE AGDA2HS Useful' unboxed #-}
  {-# COMPILE AGDA2HS Useful newtype deriving (Show) #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where

  -- The original definition of usefulness in the paper
  record OriginalUseful : Type where
    constructor ⟪_,_,_⟫
    field
      witness : Values αs0
      @0 pmat⋠witness : pmat ⋠ᵐ witness
      @0 ps≼witness : ps ≼* witness


module _
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {αs} {pmat : PatternMatrix αs} {ps : Patterns αs}
  where

  -- Our extended definition of usefulness implies the original one
  -- assuming the non-empty axiom
  Useful→OriginalUseful : Useful pmat ps → OriginalUseful pmat ps
  Useful→OriginalUseful record { witnesses = ⟪ qs , disj , subs ⟫ ∷ _ } = record
    { witness = examplesFor qs
    ; pmat⋠witness = λ h → disj h (examplesFor≼ qs)
    ; ps≼witness = subsumes subs (examplesFor≼ qs)
    }


module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where

  -- The original definition of usefulness implies our extended one
  OriginalUseful→Useful : OriginalUseful pmat ps → Useful pmat ps
  OriginalUseful→Useful ⟪ vs , ninsts , insts ⟫ = record
    { witnesses =
        ⟪ onlys vs
        , (λ h h' → ninsts (subst (λ vs → pmat ≼ᵐ vs) (sym (onlys≼⇒≡ h')) h))
        , ⊆onlys insts ⟫
        ∷ []
    }
