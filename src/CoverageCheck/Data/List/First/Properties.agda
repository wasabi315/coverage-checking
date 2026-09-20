module CoverageCheck.Data.List.First.Properties where

open import Haskell.Prelude hiding (a)

open import CoverageCheck.Data.List.First.Core
open import CoverageCheck.Extra.DecP

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

firstDecP : ∀ {a} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → (∀ xs → DecP (First p xs))
firstDecP f []       = No λ _ → undefined
firstDecP f (x ∷ xs) = ifDecP (f x)
  (λ ⦃ p ⦄ → Yes (FHere p))
  (λ ⦃ ¬p ⦄ → mapDecP (FThere ¬p) (tailFirst ¬p) (firstDecP f xs))
{-# COMPILE AGDA2HS firstDecP #-}
