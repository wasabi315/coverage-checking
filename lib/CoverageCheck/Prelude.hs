{-# LANGUAGE ScopedTypeVariables #-}
module CoverageCheck.Prelude where

import Data.List.NonEmpty (NonEmpty((:|)))

data All p = Nil
           | (:>) p (All p)
               deriving (Eq, Show)

headAll :: forall p . All p -> p
headAll (h :> _) = h

tailAll :: forall p . All p -> All p
tailAll (_ :> hs) = hs

data HAll2 r = HNil
             | (:>>) r (HAll2 r)
                 deriving (Eq, Show)

data Any p = Here p
           | There (Any p)
               deriving Show

data First p = FHere p
             | FThere (First p)
                 deriving Show

firstToAny :: forall p . First p -> Any p
firstToAny (FHere h) = Here h
firstToAny (FThere h) = There (firstToAny h)

data These a b = This a
               | That b
               | Both a b
                   deriving (Eq, Show)

these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these f g h (This x) = f x
these f g h (That x) = g x
these f g h (Both x y) = h x y

mapThese :: (a -> b) -> (c -> d) -> These a c -> These b d
mapThese f g (This x) = This (f x)
mapThese f g (That x) = That (g x)
mapThese f g (Both x y) = Both (f x) (g y)

concatNonEmpty :: NonEmpty (NonEmpty a) -> NonEmpty a
concatNonEmpty (xs :| xss) = go xs xss
  where
    go :: NonEmpty a -> [NonEmpty a] -> NonEmpty a
    go xs [] = xs
    go xs (ys : xss) = xs <> go ys xss

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
  = ifDecP (f x) (\ h -> Yes (FHere h))
      (mapDecP FThere (firstDecP f xs))

