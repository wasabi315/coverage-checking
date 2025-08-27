{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}
module CoverageCheck.Prelude where

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f g (Left x) = Left (f x)
mapEither f g (Right y) = Right (g y)

data All p = AllNil
           | AllCons p (All p)
               deriving Show

headAll :: All p -> p
headAll (AllCons h _) = h

tailAll :: All p -> All p
tailAll (AllCons _ hs) = hs

data Any p = AnyHere p
           | AnyThere (Any p)
               deriving Show

data First p = FirstHere p
             | FirstThere (First p)
                 deriving Show

firstToAny :: First p -> Any p
firstToAny (FirstHere h) = AnyHere h
firstToAny (FirstThere h) = AnyThere (firstToAny h)

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

instance Functor NonEmpty where
    fmap f (MkNonEmpty x xs) = MkNonEmpty (f x) (map f xs)

instance Applicative NonEmpty where
    pure x = MkNonEmpty x []
    MkNonEmpty f fs <*> MkNonEmpty x xs
      = MkNonEmpty (f x) (map f xs ++ (fs <*> xs))
    pure x = MkNonEmpty x []
    MkNonEmpty f fs <*> MkNonEmpty x xs
      = MkNonEmpty (f x) (map f xs ++ (fs <*> xs))

instance Monad NonEmpty where
    MkNonEmpty x xs >>= f
      = case f x of
            MkNonEmpty y ys -> MkNonEmpty y
                                 (ys ++
                                    (xs >>=
                                       \case
                                           MkNonEmpty x xs -> x : xs
                                         . f))

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
  = ifDecP (f x) (\ h -> Yes (FirstHere h))
      (mapDecP FirstThere (firstDecP f xs))

