module CoverageCheck.Data.List.All.Core where

open import Haskell.Prelude hiding (All; a)

infixr 5 _:>_

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data All (p : @0 a → Type) : (@0 xs : List a) → Type where
  Nil  : All p []
  _:>_ : p x → All p xs → All p (x ∷ xs)

{-# COMPILE AGDA2HS All deriving (Eq, Show) #-}

headAll : All p (x ∷ xs) → p x
headAll (p :> _) = p
{-# COMPILE AGDA2HS headAll #-}

tailAll : All p (x ∷ xs) → All p xs
tailAll (_ :> ps) = ps
{-# COMPILE AGDA2HS tailAll #-}

mapAll : (∀ {@0 x} → p x → q x) → (∀ {@0 xs} → All p xs → All q xs)
mapAll f Nil = Nil
mapAll f (p :> ps) = f p :> mapAll f ps
