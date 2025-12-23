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
  infix -1 _,_,_

  record Useful' : Type where
    no-eta-equality
    pattern
    constructor _,_,_
    field
      witness : Patterns αs0
      -- pmat and witness are disjoint, i.e. they have no common instances
      @0 pmat#witness : ∀ {vs} → vs ≼ᵐ pmat → vs ≼* witness → ⊥
      -- ps subsumes witness
      @0 witness⊆ps : witness ⊆* ps

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
  infix -1 _,_,_

  -- The original definition of usefulness in the paper
  record OriginalUseful : Type where
    constructor _,_,_
    field
      witness : Values αs0
      @0 witness⋠pmat : witness ⋠ᵐ pmat
      @0 witness≼ps : witness ≼* ps


module _
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {αs} {pmat : PatternMatrix αs} {ps : Patterns αs}
  where

  -- Our extended definition of usefulness implies the original one
  -- assuming the non-empty axiom
  Useful→OriginalUseful : Useful pmat ps → OriginalUseful pmat ps
  Useful→OriginalUseful record { witnesses = (qs , disj , subs) ∷ _ } =
    examplesFor qs ,
    (λ h → disj h (examplesFor≼ qs)) ,
    subsumes subs (examplesFor≼ qs)


module _ ⦃ @0 sig : Signature ⦄
  {@0 αs0} (@0 pmat : PatternMatrix αs0) (@0 ps : Patterns αs0)
  where

  -- The original definition of usefulness implies our extended one
  -- Together with Useful→OriginalUseful, this shows the equivalence of the two definitions
  -- of usefulness under the non-empty axiom
  OriginalUseful→Useful : OriginalUseful pmat ps → Useful pmat ps
  OriginalUseful→Useful (vs , ninsts , insts) = record
    { witnesses =
        ( onlys vs
        , (λ h h' → ninsts (subst (λ vs → vs ≼ᵐ pmat) (onlys≼⇒≡ h') h))
        , ⊆onlys insts )
        ∷ []
    }
