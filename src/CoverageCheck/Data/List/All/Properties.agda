module CoverageCheck.Data.List.All.Properties where

open import Haskell.Prelude hiding (All; Any; a)

open import CoverageCheck.Data.List.All.Core
open import CoverageCheck.Data.List.Any.Core
open import CoverageCheck.Extra.Negation

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

All¬⇒¬Any : ∀ {@0 xs} → All (λ x → ¬ p x) xs → ¬ Any p xs
All¬⇒¬Any (¬p :> _)   (Here  p) = ¬p p
All¬⇒¬Any (_  :> ¬ps) (There p) = All¬⇒¬Any ¬ps p

¬Any⇒All¬ : ∀ xs → ¬ Any p xs → All (λ x → ¬ p x) xs
¬Any⇒All¬ []       ¬p = Nil
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ Here :> ¬Any⇒All¬ xs (¬p ∘ There)
