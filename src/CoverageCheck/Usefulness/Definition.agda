open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import Haskell.Data.List.NonEmpty using (NonEmpty)

module CoverageCheck.Usefulness.Definition
  ⦃ @0 globals : Globals ⦄
  ⦃ @0 sig : Signature ⦄
  where

private open module @0 G = Globals globals

--------------------------------------------------------------------------------

module _ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) where

  record Useful' : Type where
    no-eta-equality
    pattern
    constructor ⟪_,_,_⟫
    field
      qs       : Patterns αs0
      @0 P#qs  : ∀ {vs} → P ≼** vs → qs ≼* vs → ⊥
      @0 ps⊆qs : ps ⊆* qs

  record Useful : Type where
    no-eta-equality
    field
      witnesses : NonEmpty Useful'

  open Useful public

  {-# COMPILE AGDA2HS Useful' unboxed #-}
  {-# COMPILE AGDA2HS Useful newtype deriving (Show) #-}
