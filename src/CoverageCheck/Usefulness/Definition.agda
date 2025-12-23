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
  infix -1 _,_

  record IsWitness (witness : Patterns αs0) : Type where
    no-eta-equality
    pattern
    constructor _,_
    field
      -- pmat and witness are disjoint, i.e. they have no common instances
      pmat#witness : ∀ {vs} → vs ≼ᵐ pmat → vs ≼* witness → ⊥
      -- ps subsumes witness
      witness⊆ps : witness ⊆* ps

  Useful' : Type
  Useful' = ∃[ witness ∈ _ ] IsWitness witness

  record Useful : Type where
    no-eta-equality
    pattern
    field
      witnesses : NonEmpty Useful'

  open Useful public

  {-# COMPILE AGDA2HS Useful' inline #-}
  {-# COMPILE AGDA2HS Useful newtype deriving (Show) #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where
  infix -1 _,_

  -- The original definition of usefulness in the paper

  record IsWitnessOriginal (witness : Values αs0) : Type where
    no-eta-equality
    pattern
    constructor _,_
    field
      witness⋠pmat : witness ⋠ᵐ pmat
      witness≼ps : witness ≼* ps

  OriginalUseful : Type
  OriginalUseful = ∃[ witness ∈ _ ] IsWitnessOriginal witness


module _
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {αs} {pmat : PatternMatrix αs} {ps : Patterns αs}
  where

  -- Our extended definition of usefulness implies the original one
  -- assuming the non-empty axiom
  Useful→OriginalUseful : Useful pmat ps → OriginalUseful pmat ps
  Useful→OriginalUseful record { witnesses = (qs ⟨ disj , subs ⟩) ∷ _ } =
    examplesFor qs
      ⟨ (λ h → disj h (examplesFor≼ qs)) , subsumes subs (examplesFor≼ qs) ⟩


module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where

  -- The original definition of usefulness implies our extended one
  -- Together with Useful→OriginalUseful, this shows the equivalence of the two definitions
  -- of usefulness under the non-empty axiom
  OriginalUseful→Useful : OriginalUseful pmat ps → Useful pmat ps
  OriginalUseful→Useful (vs ⟨ ninsts , insts ⟩) = record
    { witnesses =
        (onlys vs
          ⟨ (λ h h' → ninsts (subst (λ vs → vs ≼ᵐ pmat) (onlys≼⇒≡ h') h))
          , ⊆onlys insts ⟩)
        ∷ []
    }
