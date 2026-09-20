module Haskell.Data.Foldable1 where

open import Haskell.Prim using (Type; id; _∘_)
open import Haskell.Prim.Functor using (Functor)
open import Haskell.Prim.Monoid using (Semigroup; _<>_)
open import Haskell.Prim.Foldable using (Foldable)

--------------------------------------------------------------------------------

record Foldable1 (p : Type → Type) : Type₁ where
  field
    ⦃ super ⦄ : Foldable p
    foldMap1  : ∀ {a m} ⦃ _ : Semigroup m ⦄ → (a → m) → p a → m

open Foldable1 ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Foldable1 existing-class #-}
