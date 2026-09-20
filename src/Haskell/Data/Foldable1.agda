module Haskell.Data.Foldable1 where

open import Haskell.Prelude

--------------------------------------------------------------------------------

record Foldable1 (p : Type → Type) : Type₁ where
  field
    ⦃ super ⦄ : Foldable p
    foldMap1  : ∀ {a m} ⦃ _ : Semigroup m ⦄ → (a → m) → p a → m

open Foldable1 ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Foldable1 existing-class #-}
