{-# LANGUAGE ScopedTypeVariables #-}
module CoverageCheck.Prelude where

import Data.Bifoldable (Bifoldable)
import Data.Bifoldable1 (Bifoldable1)
import Data.Bifunctor (Bifunctor)
import Data.List.NonEmpty (NonEmpty((:|)))

import Data.Bifoldable (Bifoldable(..))
import Data.Bifoldable1 (Bifoldable1(..))
import Data.Bifunctor (Bifunctor(..))

data All p = Nil
           | (:>) p (All p)
               deriving (Eq, Show)

data Any p = Here p
           | There (Any p)
               deriving (Eq, Show)

data First p = FHere p
             | FThere (First p)
                 deriving (Eq, Show)

data HPointwise r = HNil
                  | (:>>) r (HPointwise r)
                      deriving (Eq, Show)

headAll :: forall p . All p -> p
headAll (p :> _) = p

tailAll :: forall p . All p -> All p
tailAll (_ :> ps) = ps

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

data DecP a = Yes a
            | No
                deriving Show

mapDecP :: (a -> b) -> DecP a -> DecP b
mapDecP f (Yes p) = Yes (f p)
mapDecP f No = No

ifDecP :: DecP a -> (a -> b) -> b -> b
ifDecP (Yes p) t e = t p
ifDecP No t e = e

infix 3 `tupleDecP`
tupleDecP :: DecP a -> DecP b -> DecP (a, b)
tupleDecP No _ = No
tupleDecP (Yes _) No = No
tupleDecP (Yes p) (Yes q) = Yes (p, q)

eitherDecP :: DecP a -> DecP b -> DecP (Either a b)
eitherDecP (Yes p) _ = Yes (Left p)
eitherDecP No (Yes q) = Yes (Right q)
eitherDecP No No = No

theseDecP :: DecP a -> DecP b -> DecP (These a b)
theseDecP (Yes p) (Yes q) = Yes (Both p q)
theseDecP (Yes p) No = Yes (This p)
theseDecP No (Yes q) = Yes (That q)
theseDecP No No = No

firstDecP :: (a -> DecP p) -> [a] -> DecP (First p)
firstDecP f [] = No
firstDecP f (x : xs)
  = ifDecP (f x) (\ p -> Yes (FHere p))
      (mapDecP FThere (firstDecP f xs))

