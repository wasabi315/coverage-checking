module CoverageCheck.Data.List.First.Core where

open import Haskell.Prelude hiding (a)

open import CoverageCheck.Extra.Negation

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data First (p : @0 a → Type) : (@0 xs : List a) → Type where
  FHere  : p x → First p (x ∷ xs)
  FThere : @0 ¬ p x → First p xs → First p (x ∷ xs)

{-# COMPILE AGDA2HS First deriving (Eq, Show) #-}

tailFirst : ¬ p x → First p (x ∷ xs) → First p xs
tailFirst ¬p (FHere p) = contradiction p ¬p
tailFirst ¬p (FThere _ p) = p
