module Haskell.Data.Bifoldable where

open import Haskell.Prim using (Type; id; _∘_)
open import Haskell.Prim.Functor using (Functor)
open import Haskell.Prim.Monoid using (Monoid; MonoidEndo; _<>_; mempty)
open import Haskell.Prim.Tuple using (_×_; _,_; fst; snd)
open import Haskell.Prim.Either using (Either; Left; Right)

--------------------------------------------------------------------------------

record Bifoldable (p : Type → Type → Type) : Type₁ where
  field
    bifoldMap : ∀ {a b m} ⦃ _ : Monoid m ⦄ → (a → m) → (b → m) → p a b → m
    bifoldr   : {a b c : Type} → (a → c → c) → (b → c → c) → c → p a b → c

  bifold : ∀ {m} ⦃ _ : Monoid m ⦄ → p m m → m
  bifold = bifoldMap id id

record BifoldableFromBifoldMap (p : Type → Type → Type) : Type₁ where
  field
    bifoldMap : ∀ {a b m} ⦃ _ : Monoid m ⦄ → (a → m) → (b → m) → p a b → m

  bifoldr : {a b c : Type} → (a → c → c) → (b → c → c) → c → p a b → c
  bifoldr f g z t = bifoldMap ⦃ MonoidEndo ⦄ f g t z

record BifoldableFromBifoldr (p : Type → Type → Type) : Type₁ where
  field
    bifoldr : {a b c : Type} → (a → c → c) → (b → c → c) → c → p a b → c

  bifoldMap : ∀ {a b m} ⦃ _ : Monoid m ⦄ → (a → m) → (b → m) → p a b → m
  bifoldMap f g = bifoldr (_<>_ ∘ f) (_<>_ ∘ g) mempty

open Bifoldable ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Bifoldable existing-class #-}

--------------------------------------------------------------------------------

instance

  iBifoldableFromBifoldMapTuple : BifoldableFromBifoldMap _×_
  iBifoldableFromBifoldMapTuple .BifoldableFromBifoldMap.bifoldMap f g (x , y) = f x <> g y

  iBifoldableTuple : Bifoldable _×_
  iBifoldableTuple = record {BifoldableFromBifoldMap iBifoldableFromBifoldMapTuple}

  iBifoldableFromBifoldMapEither : BifoldableFromBifoldMap Either
  iBifoldableFromBifoldMapEither .BifoldableFromBifoldMap.bifoldMap f g (Left x)  = f x
  iBifoldableFromBifoldMapEither .BifoldableFromBifoldMap.bifoldMap f g (Right y) = g y

  iBifoldableEither : Bifoldable Either
  iBifoldableEither = record {BifoldableFromBifoldMap iBifoldableFromBifoldMapEither}
