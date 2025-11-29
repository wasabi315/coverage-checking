module Haskell.Data.Bifunctor where

open import Haskell.Prim using (Type; id; _∘_)
open import Haskell.Prim.Functor using (Functor)
open import Haskell.Prim.Tuple using (_×_; _,_; fst; snd)
open import Haskell.Prim.Either using (Either; Left; Right)

--------------------------------------------------------------------------------

record Bifunctor (p : Type → Type → Type) : Type₁ where
  field
    overlap ⦃ super ⦄ : ∀ {a} → Functor (p a)
    bimap : ∀ {a b c d} → (a → b) → (c → d) → p a c → p b d
    first : ∀ {a b c} → (a → b) → p a c → p b c
    second : ∀ {a b c} → (b → c) → p a b → p a c

record BifunctorFromBimap (p : Type → Type → Type) : Type₁ where
  field
    overlap ⦃ super ⦄ : ∀ {a} → Functor (p a)
    bimap : ∀ {a b c d} → (a → b) → (c → d) → p a c → p b d

  first : ∀ {a b c} → (a → b) → p a c → p b c
  first f = bimap f id

  second : ∀ {a b c} → (b → c) → p a b → p a c
  second = bimap id

record BifunctorFromFirstSecond (p : Type → Type → Type) : Type₁ where
  field
    overlap ⦃ super ⦄ : ∀ {a} → Functor (p a)
    first : ∀ {a b c} → (a → b) → p a c → p b c
    second : ∀ {a b c} → (b → c) → p a b → p a c

  bimap : ∀ {a b c d} → (a → b) → (c → d) → p a c → p b d
  bimap f g = first f ∘ second g

open Bifunctor ⦃...⦄ public

{-# COMPILE AGDA2HS Bifunctor existing-class #-}

--------------------------------------------------------------------------------

instance

  iBifunctorFromBimapTuple : BifunctorFromBimap _×_
  iBifunctorFromBimapTuple .BifunctorFromBimap.bimap f g p = f (p .fst) , g (p .snd)

  iBifunctorTuple : Bifunctor _×_
  iBifunctorTuple = record{BifunctorFromBimap iBifunctorFromBimapTuple}

  iBifunctorFromBimapEither : BifunctorFromBimap Either
  iBifunctorFromBimapEither .BifunctorFromBimap.bimap f _ (Left x) = Left (f x)
  iBifunctorFromBimapEither .BifunctorFromBimap.bimap _ g (Right x) = Right (g x)

  iBifunctorEither : Bifunctor Either
  iBifunctorEither = record{BifunctorFromBimap iBifunctorFromBimapEither}
