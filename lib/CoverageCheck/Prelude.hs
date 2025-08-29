{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module CoverageCheck.Prelude where

import Control.Arrow (first)

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f g (Left x) = Left (f x)
mapEither f g (Right y) = Right (g y)

data All p = Nil
           | Cons p (All p)
               deriving (Eq, Show)

headAll :: forall p . All p -> p
headAll (Cons h _) = h

tailAll :: forall p . All p -> All p
tailAll (Cons _ hs) = hs

infixr 5 `appendAll`
appendAll :: forall p . All p -> All p -> All p
appendAll Nil ys = ys
appendAll (Cons x xs) ys = Cons x (appendAll xs ys)

data HAll2 r = HNil
             | HCons r (HAll2 r)
                 deriving (Eq, Show)

hUncons :: forall r . HAll2 r -> (r, HAll2 r)
hUncons (HCons h hs) = (h, hs)

infixr 5 `hAppend`
hAppend :: forall r . HAll2 r -> HAll2 r -> HAll2 r
hAppend HNil ys = ys
hAppend (HCons x xs) ys = HCons x (hAppend xs ys)

infixr 5 `hUnappend`
hUnappend :: forall p r . All p -> HAll2 r -> (HAll2 r, HAll2 r)
hUnappend Nil xs = (HNil, xs)
hUnappend (Cons hp hps) (HCons x xs)
  = first (HCons x) (hUnappend hps xs)

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

data NonEmpty a = MkNonEmpty{head :: a, tail :: [a]}
                    deriving Show

infixr 5 `consNonEmpty`
consNonEmpty :: a -> NonEmpty a -> NonEmpty a
consNonEmpty x (MkNonEmpty y ys) = MkNonEmpty x (y : ys)

bindNonEmpty :: NonEmpty a -> (a -> NonEmpty b) -> NonEmpty b
bindNonEmpty (MkNonEmpty x xs) f
  = case f x of
        MkNonEmpty y ys -> MkNonEmpty y
                             (ys ++
                                (xs >>=
                                   \case
                                       MkNonEmpty x xs -> x : xs
                                     . f))

instance Functor NonEmpty where
    fmap f (MkNonEmpty x xs) = MkNonEmpty (f x) (map f xs)

instance Applicative NonEmpty where
    pure x = MkNonEmpty x []
    fs <*> xs
      = bindNonEmpty fs (\ f -> bindNonEmpty xs (\ x -> pure (f x)))
    xs <* ys = bindNonEmpty xs (\ x -> bindNonEmpty ys (\ _ -> pure x))
    xs *> ys = bindNonEmpty xs (\ _ -> bindNonEmpty ys pure)

instance Monad NonEmpty where
    (>>=) = bindNonEmpty

instance Semigroup (NonEmpty a) where
    MkNonEmpty x xs <> MkNonEmpty y ys = MkNonEmpty x (xs ++ (y : ys))

concatNonEmpty :: NonEmpty (NonEmpty a) -> NonEmpty a
concatNonEmpty (MkNonEmpty xs xss) = go xs xss
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

