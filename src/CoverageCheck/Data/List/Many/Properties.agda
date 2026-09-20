module CoverageCheck.Data.List.Many.Properties where

open import Haskell.Prelude hiding (a)

open import CoverageCheck.Data.List.Many.Core
open import CoverageCheck.Extra.DecP

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

manyDecP : {a : Type} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → ∀ xs → DecP (Many p xs)
manyDecP f [] = Yes MNil
manyDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (MHere px) tailMany (manyDecP f xs))
    (mapDecP MThere tailMany (manyDecP f xs))
{-# COMPILE AGDA2HS manyDecP #-}
