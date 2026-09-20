module CoverageCheck.Data.List.Any.Properties where

open import Haskell.Prelude hiding (Any; a)

open import Haskell.Data.Bifunctor
open import CoverageCheck.Data.List.Any.Core
open import CoverageCheck.Data.List.First.Core
open import CoverageCheck.Extra.Negation

private
  variable
    @0 a : Type
    p q : @0 a → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

First⇒Any : First p xs → Any p xs
First⇒Any (FHere p)   = Here p
First⇒Any (FThere _ ps) = There (First⇒Any ps)

¬First⇒¬Any : ¬ First p xs → ¬ Any p xs
¬First⇒¬Any ¬p (Here p)  = ¬p (FHere p)
¬First⇒¬Any ¬p (There p) = ¬First⇒¬Any (¬p ∘ FThere (¬p ∘ FHere)) p

module _ {@0 a : Type} {p : @0 a → Type} where

  ++Any⁺ˡ : ∀ {@0 xs ys} → Any p xs → Any p (xs ++ ys)
  ++Any⁺ˡ (Here p)  = Here p
  ++Any⁺ˡ (There p) = There (++Any⁺ˡ p)

  ++Any⁺ʳ : ∀ {xs} {@0 ys} → Any p ys → Any p (xs ++ ys)
  ++Any⁺ʳ {[]}     p = p
  ++Any⁺ʳ {x ∷ xs} p = There (++Any⁺ʳ p)

  ++Any⁻ : ∀ xs {@0 ys} → Any p (xs ++ ys) → Either (Any p xs) (Any p ys)
  ++Any⁻ []       p         = Right p
  ++Any⁻ (x ∷ xs) (Here p)  = Left (Here p)
  ++Any⁻ (x ∷ xs) (There p) = bimap There id (++Any⁻ xs p)


module _ {@0 f : a → b} where

  gmapAny⁺
    : (∀ {x} → p x → q (f x))
    → (∀ {xs} → Any p xs → Any q (map f xs))
  gmapAny⁺ g {x ∷ xs} (Here p)  = Here (g p)
  gmapAny⁺ g {x ∷ xs} (There p) = There (gmapAny⁺ g p)

  gmapAny⁻
    : (∀ {x} → q (f x) → p x)
    → (∀ {xs} → Any q (map f xs) → Any p xs)
  gmapAny⁻ g {x ∷ xs} (Here p)  = Here (g p)
  gmapAny⁻ g {x ∷ xs} (There p) = There (gmapAny⁻ g p)


module _ {f : a → List b} where

  gconcatMapAny⁺
    : (∀ {x} → p x → Any q (f x))
    → (∀ {xs} → Any p xs → Any q (concatMap f xs))
  gconcatMapAny⁺ g {x ∷ xs} (Here p)  = ++Any⁺ˡ (g p)
  gconcatMapAny⁺ g {x ∷ xs} (There p) = ++Any⁺ʳ (gconcatMapAny⁺ g p)

  gconcatMapAny⁻
    : (∀ {x} → Any q (f x) → p x)
    → (∀ {xs : List _} → Any q (concatMap f xs) → Any p xs)
  gconcatMapAny⁻ g {x ∷ xs} p with ++Any⁻ (f x) p
  ... | Left q  = Here (g q)
  ... | Right q = There (gconcatMapAny⁻ g q)

