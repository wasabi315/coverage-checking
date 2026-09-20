module CoverageCheck.Data.List.Some.Properties where

open import Haskell.Prelude hiding (All; a)

open import CoverageCheck.Data.List.All.Core
open import CoverageCheck.Data.List.Many.Core
open import CoverageCheck.Data.List.Many.Properties
open import CoverageCheck.Data.List.Some.Core
open import CoverageCheck.Extra.Negation
open import CoverageCheck.Extra.DecP

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

¬Some⇒All¬ : ∀ xs → ¬ Some p xs → All (λ x → ¬ p x) xs
¬Some⇒All¬ [] _ = Nil
¬Some⇒All¬ (x ∷ xs) ¬pxxs =
  (λ px → ¬pxxs (SHere px (trivialMany xs))) :> ¬Some⇒All¬ xs (¬pxxs ∘ SThere)

someDecP : {a : Type} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → ∀ xs → DecP (Some p xs)
someDecP f [] = No λ _ → undefined
someDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (SHere px) tailSome (manyDecP f xs))
    (λ ⦃ ¬px ⦄ → mapDecP SThere (unthereSome ¬px) (someDecP f xs))
{-# COMPILE AGDA2HS someDecP #-}
