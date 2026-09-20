module CoverageCheck.Data.List.Some.Core where

open import Haskell.Prelude hiding (a)

open import CoverageCheck.Data.List.Many.Core
open import CoverageCheck.Extra.Negation

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data Some (p : @0 a → Type) : (@0 xs : List a) → Type where
  SHere  : p x → Many p xs → Some p (x ∷ xs)
  SThere : Some p xs → Some p (x ∷ xs)

{-# COMPILE AGDA2HS Some deriving (Eq, Show) #-}

someToMany : ∀ {@0 xs} → Some p xs → Many p xs
someToMany (SHere px pxs) = MHere px pxs
someToMany (SThere pxs)   = MThere (someToMany pxs)
{-# COMPILE AGDA2HS someToMany #-}

tailSome : ∀ {@0 x xs} → Some p (x ∷ xs) → Many p xs
tailSome (SHere px pxs) = pxs
tailSome (SThere pxs)   = someToMany pxs
{-# COMPILE AGDA2HS tailSome #-}

unthereSome : @0 ¬ p x → Some p (x ∷ xs) → Some p xs
unthereSome ¬px (SHere px pxs) = contradiction px ¬px
unthereSome ¬px (SThere pxs)   = pxs
{-# COMPILE AGDA2HS unthereSome #-}
