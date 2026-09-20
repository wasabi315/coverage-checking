module CoverageCheck.Data.List.Many.Core where

open import Haskell.Prelude hiding (a)

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data Many (p : @0 a → Type) : (@0 xs : List a) → Type where
  MNil   : Many p []
  MHere  : p x → Many p xs → Many p (x ∷ xs)
  MThere : Many p xs → Many p (x ∷ xs)

{-# COMPILE AGDA2HS Many deriving (Eq, Show) #-}

tailMany : ∀ {@0 x xs} → Many p (x ∷ xs) → Many p xs
tailMany (MHere _ ps) = ps
tailMany (MThere ps)  = ps
{-# COMPILE AGDA2HS tailMany #-}

trivialMany : ∀ xs → Many p xs
trivialMany []       = MNil
trivialMany (_ ∷ xs) = MThere (trivialMany xs)
