module CoverageCheck.Data.These where

open import Haskell.Prelude hiding (NonEmpty)

open import Haskell.Data.Bifoldable
open import Haskell.Data.Bifoldable1
open import Haskell.Data.Bifunctor
open import Haskell.Data.List.NonEmpty

{-# FOREIGN AGDA2HS
import Data.Bifoldable (Bifoldable(..))
import Data.Bifoldable1 (Bifoldable1(..))
import Data.Bifunctor (Bifunctor(..))
#-}

--------------------------------------------------------------------------------

data These (a b : Type) : Type where
  This  : a → These a b
  That  : b → These a b
  Both  : a → b → These a b

{-# COMPILE AGDA2HS These deriving (Eq, Show) #-}

these : {a b c : Type} → (a → c) → (b → c) → (a → b → c) → These a b → c
these f g h (This x)   = f x
these f g h (That x)   = g x
these f g h (Both x y) = h x y
{-# COMPILE AGDA2HS these #-}

eitherToThese : {a b : Type} → Either a b → These a b
eitherToThese = either This That
{-# COMPILE AGDA2HS eitherToThese inline #-}

partitionEithersNonEmpty : {a b : Type}
  → NonEmpty (Either a b)
  → These (NonEmpty a) (NonEmpty b)
partitionEithersNonEmpty {a} {b} (x :| xs) = go x xs
  where
    ext : Either a b → These (NonEmpty a) (NonEmpty b) → These (NonEmpty a) (NonEmpty b)
    ext (Left x)  (This xs)    = This (x <| xs)
    ext (Left x)  (That ys)    = Both (x :| []) ys
    ext (Left x)  (Both xs ys) = Both (x <| xs) ys
    ext (Right y) (This xs)    = Both xs (y :| [])
    ext (Right y) (That ys)    = That (y <| ys)
    ext (Right y) (Both xs ys) = Both xs (y <| ys)

    go : Either a b → List (Either a b) → These (NonEmpty a) (NonEmpty b)
    go x         (y ∷ xs) = ext x (go y xs)
    go (Left x)  []       = This (x :| [])
    go (Right y) []       = That (y :| [])

instance
  iDefaultFunctorThese : ∀ {a} → DefaultFunctor (These a)
  iDefaultFunctorThese .DefaultFunctor.fmap f (This x) = This x
  iDefaultFunctorThese .DefaultFunctor.fmap f (That y) = That (f y)
  iDefaultFunctorThese .DefaultFunctor.fmap f (Both x y) = Both x (f y)

  iFunctorThese : ∀ {a} → Functor (These a)
  iFunctorThese = record {DefaultFunctor iDefaultFunctorThese}
  {-# COMPILE AGDA2HS iFunctorThese #-}

  iBifunctorFromBimapThese : BifunctorFromBimap These
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (This x) = This (f x)
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (That y) = That (g y)
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (Both x y) = Both (f x) (g y)

  iBifunctorThese : Bifunctor These
  iBifunctorThese = record {BifunctorFromBimap iBifunctorFromBimapThese}
  {-# COMPILE AGDA2HS iBifunctorThese #-}

  iBifoldableFromBifoldMapThese : BifoldableFromBifoldMap These
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (This x) = f x
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (That y) = g y
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (Both x y) = f x <> g y

  iBifoldableThese : Bifoldable These
  iBifoldableThese = record {BifoldableFromBifoldMap iBifoldableFromBifoldMapThese}
  {-# COMPILE AGDA2HS iBifoldableThese #-}

  iBifoldable1These : Bifoldable1 These
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (This x) = f x
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (That y) = g y
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (Both x y) = f x <> g y
  {-# COMPILE AGDA2HS iBifoldable1These #-}

  iSemigroupThese : ∀ {a b} → ⦃ Semigroup a ⦄ → ⦃ Semigroup b ⦄ → Semigroup (These a b)
  iSemigroupThese ._<>_ (This x)   (This x')    = This (x <> x')
  iSemigroupThese ._<>_ (This x)   (That y')    = Both x y'
  iSemigroupThese ._<>_ (This x)   (Both x' y') = Both (x <> x') y'
  iSemigroupThese ._<>_ (That y)   (This x')    = Both x' y
  iSemigroupThese ._<>_ (That y)   (That y')    = That (y <> y')
  iSemigroupThese ._<>_ (That y)   (Both x' y') = Both x' (y <> y')
  iSemigroupThese ._<>_ (Both x y) (This x')    = Both (x <> x') y
  iSemigroupThese ._<>_ (Both x y) (That y')    = Both x (y <> y')
  iSemigroupThese ._<>_ (Both x y) (Both x' y') = Both (x <> x') (y <> y')
  {-# COMPILE AGDA2HS iSemigroupThese #-}
