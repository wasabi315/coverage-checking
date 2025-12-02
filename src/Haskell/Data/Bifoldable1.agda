module Haskell.Data.Bifoldable1 where

open import Haskell.Prim using (Type; id; _∘_)
open import Haskell.Prim.Functor using (Functor)
open import Haskell.Prim.Monoid using (Semigroup; MonoidEndo; _<>_; mempty)
open import Haskell.Prim.Tuple using (_×_; _,_; fst; snd)
open import Haskell.Prim.Either using (Either; Left; Right)

open import Haskell.Data.Bifoldable using (Bifoldable)

--------------------------------------------------------------------------------

record Bifoldable1 (p : Type → Type → Type) : Type₁ where
  field
    ⦃ super ⦄  : Bifoldable p
    bifoldMap1 : ∀ {a b m} ⦃ _ : Semigroup m ⦄ → (a → m) → (b → m) → p a b → m

  bifold1 : ∀ {m} ⦃ _ : Semigroup m ⦄ → p m m → m
  bifold1 = bifoldMap1 id id

open Bifoldable1 ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Bifoldable1 existing-class #-}

--------------------------------------------------------------------------------

instance

  iBifoldable1Tuple : Bifoldable1 _×_
  iBifoldable1Tuple .Bifoldable1.bifoldMap1 f g (x , y) = f x <> g y

  iBifoldable1Either : Bifoldable1 Either
  iBifoldable1Either .Bifoldable1.bifoldMap1 f g (Left x)  = f x
  iBifoldable1Either .Bifoldable1.bifoldMap1 f g (Right y) = g y
