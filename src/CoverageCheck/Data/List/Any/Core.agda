module CoverageCheck.Data.List.Any.Core where

open import Haskell.Prelude hiding (Any; a)

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data Any (p : @0 a → Type) : (@0 xs : List a) → Type where
  Here  : p x → Any p (x ∷ xs)
  There : Any p xs → Any p (x ∷ xs)

{-# COMPILE AGDA2HS Any deriving (Eq, Show) #-}
