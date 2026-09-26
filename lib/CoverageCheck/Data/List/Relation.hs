{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module CoverageCheck.Data.List.Relation where

import CoverageCheck.Extra.DecP (DecP(No, Yes), ifDecP, mapDecP)
import Numeric.Natural (Natural)

wInvIsSuc :: Natural -> (Natural -> f) -> f
wInvIsSuc m g = g m

inThere :: Natural -> Natural
inThere n = succ n

type Any a = (Natural, a)

wRecAny :: forall a f . (a -> f) -> (f -> f) -> Natural -> a -> f
wRecAny h t n q
  = if n == 0 then h q else
      wInvIsSuc (pred n) (\ n -> t (wRecAny h t n q))

wInvIsSucF :: Natural -> (Natural -> f) -> f
wInvIsSucF m g = g m

type First a = (Natural, a)

firstDecP :: (e -> DecP a) -> [e] -> DecP (First a)
firstDecP f [] = No
firstDecP f (x : xs)
  = ifDecP (f x) (\ p -> Yes (0, p))
      (mapDecP
         (\case
              (n, r) -> (succ n, r))
         (firstDecP f xs))

wRecFirst :: forall a f . (a -> f) -> (f -> f) -> Natural -> a -> f
wRecFirst h t n q
  = if n == 0 then h q else
      wInvIsSucF (pred n) (\ n -> t (wRecFirst h t n q))

data Many a = MNil
            | MHere a (Many a)
            | MThere (Many a)
                deriving (Eq, Show)

tailMany :: Many a -> Many a
tailMany (MHere _ xs) = xs
tailMany (MThere xs) = xs

manyDecP :: (e -> DecP a) -> [e] -> DecP (Many a)
manyDecP f [] = Yes MNil
manyDecP f (x : xs)
  = ifDecP (f x) (\ px -> mapDecP (MHere px) (manyDecP f xs))
      (mapDecP MThere (manyDecP f xs))

data Some a = SHere a (Many a)
            | SThere (Some a)
                deriving (Eq, Show)

someToMany :: Some a -> Many a
someToMany (SHere x xs) = MHere x xs
someToMany (SThere xs) = MThere (someToMany xs)

tailSome :: Some a -> Many a
tailSome (SHere x xs) = xs
tailSome (SThere xs) = someToMany xs

unthereSome :: Some a -> Some a
unthereSome (SHere x xs) = undefined
unthereSome (SThere xs) = xs

someDecP :: (e -> DecP a) -> [e] -> DecP (Some a)
someDecP f [] = No
someDecP f (x : xs)
  = ifDecP (f x) (\ px -> mapDecP (SHere px) (manyDecP f xs))
      (mapDecP SThere (someDecP f xs))

