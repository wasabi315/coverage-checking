module CoverageCheck.Data.These where

import Data.Bifoldable (Bifoldable)
import Data.Bifoldable1 (Bifoldable1)
import Data.Bifunctor (Bifunctor)

import Data.Bifoldable (Bifoldable(..))
import Data.Bifoldable1 (Bifoldable1(..))
import Data.Bifunctor (Bifunctor(..))

data These a b = This a
               | That b
               | Both a b
                   deriving (Eq, Show)

these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these f g h (This x) = f x
these f g h (That x) = g x
these f g h (Both x y) = h x y

instance Functor (These a) where
    fmap f (This x) = This x
    fmap f (That y) = That (f y)
    fmap f (Both x y) = Both x (f y)

instance Bifunctor These where
    bimap f g (This x) = This (f x)
    bimap f g (That y) = That (g y)
    bimap f g (Both x y) = Both (f x) (g y)

instance Bifoldable These where
    bifoldMap f g (This x) = f x
    bifoldMap f g (That y) = g y
    bifoldMap f g (Both x y) = f x <> g y

instance Bifoldable1 These where
    bifoldMap1 f g (This x) = f x
    bifoldMap1 f g (That y) = g y
    bifoldMap1 f g (Both x y) = f x <> g y

instance (Semigroup a, Semigroup b) => Semigroup (These a b) where
    This x <> This x' = This (x <> x')
    This x <> That y' = Both x y'
    This x <> Both x' y' = Both (x <> x') y'
    That y <> This x' = Both x' y
    That y <> That y' = That (y <> y')
    That y <> Both x' y' = Both x' (y <> y')
    Both x y <> This x' = Both (x <> x') y
    Both x y <> That y' = Both x (y <> y')
    Both x y <> Both x' y' = Both (x <> x') (y <> y')

