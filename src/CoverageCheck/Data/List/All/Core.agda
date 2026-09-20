module CoverageCheck.Data.List.All.Core where

open import Haskell.Prelude hiding (All)

infixr 5 _:>_

private
  variable
    @0 a0 : Type
    p q : @0 a0 → Type
    @0 x0 : a0
    @0 xs0 : List a0

--------------------------------------------------------------------------------

data All (p : @0 a0 → Type) : (@0 xs : List a0) → Type where
  Nil  : All p []
  _:>_ : ∀ {@0 x xs} → p x → All p xs → All p (x ∷ xs)

{-# COMPILE AGDA2HS All deriving (Eq, Show) #-}

headAll : All p (x0 ∷ xs0) → p x0
headAll (p :> _) = p
{-# COMPILE AGDA2HS headAll #-}

tailAll : All p (x0 ∷ xs0) → All p xs0
tailAll (_ :> ps) = ps
{-# COMPILE AGDA2HS tailAll #-}

mapAll : (∀ {@0 x} → p x → q x) → (∀ {@0 xs} → All p xs → All q xs)
mapAll f Nil = Nil
mapAll f (p :> ps) = f p :> mapAll f ps
