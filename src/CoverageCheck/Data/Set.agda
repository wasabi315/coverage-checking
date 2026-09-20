module CoverageCheck.Data.Set where

open import Haskell.Prelude hiding (NonEmpty)
open import Haskell.Law.Bool
open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement

open import Haskell.Data.List.NonEmpty as NE using (NonEmpty)

open import Data.Set as Set public hiding
  ( prop-null→empty; prop-member-fromList; prop-member-toAscList;
    prop-member-empty; prop-member-insert; prop-member-union;
    prop-member-difference; prop-member-null; prop-equality;
    prop-union-identity; prop-union-sym; prop-null-empty )

--------------------------------------------------------------------------------

private
  ||-leftFalse : (x y : Bool) → (x || y) ≡ False → x ≡ False
  ||-leftFalse False y _ = refl

module _ {a : Type} ⦃ _ : Ord a ⦄ where
  open import Agda.Builtin.Equality.Erase

  -- Wrap the postulated properties of Set with primEraseEquality.
  -- These wrapped properties reduce to refl when the sides are definitionally equal.
  -- This should not affect the validity of the proofs.

  prop-null→empty : (s : Set a) → Set.null s ≡ True → s ≡ Set.empty
  prop-null→empty s eq = primEraseEquality (Set.prop-null→empty s eq)

  prop-member-fromList : (x : a) (xs : List a)
    → Set.member x (Set.fromList xs) ≡ elem x xs
  prop-member-fromList x xs = primEraseEquality (Set.prop-member-fromList x xs)

  prop-member-toAscList : (x : a) (s : Set a)
    → elem x (Set.toAscList s) ≡ Set.member x s
  prop-member-toAscList x s = primEraseEquality (Set.prop-member-toAscList x s)

  prop-member-empty : (x : a) → Set.member x Set.empty ≡ False
  prop-member-empty x = primEraseEquality (Set.prop-member-empty x)

  prop-member-insert : ∀ (x y : a) (s : Set a)
    → Set.member x (Set.insert y s) ≡ (x == y || Set.member x s)
  prop-member-insert x y s
    rewrite primEraseEquality (Set.prop-member-insert x y s)
    with x == y
  ... | True  = refl
  ... | False = refl

  prop-member-union : ∀ (x : a) (s1 s2 : Set a)
    → Set.member x (Set.union s1 s2) ≡ (Set.member x s1 || Set.member x s2)
  prop-member-union x s1 s2 = primEraseEquality (Set.prop-member-union x s1 s2)

  prop-member-difference : ∀ (x : a) (s1 s2 : Set a)
    → Set.member x (Set.difference s1 s2) ≡ (Set.member x s1 && not (Set.member x s2))
  prop-member-difference x s1 s2 = primEraseEquality (Set.prop-member-difference x s1 s2)

  prop-member-null : (s : Set a)
    → (∀ x → Set.member x s ≡ False) → Set.null s ≡ True
  prop-member-null s eq = primEraseEquality (Set.prop-member-null s eq)

  prop-member-singleton : (x y : a)
    → Set.member x (Set.singleton y) ≡ (x == y)
  prop-member-singleton x y
    rewrite prop-member-insert x y Set.empty
    | prop-member-empty x
    = prop-x-||-False _

  prop-equality : {s1 s2 : Set a}
    → (∀ x → Set.member x s1 ≡ Set.member x s2)
    → s1 ≡ s2
  prop-equality h = primEraseEquality (Set.prop-equality h)

  prop-union-identity : {s : Set a}
    → Set.union s Set.empty ≡ s
  prop-union-identity = primEraseEquality Set.prop-union-identity

  prop-union-sym : {sa sb : Set a}
    → Set.union sa sb ≡ Set.union sb sa
  prop-union-sym = primEraseEquality Set.prop-union-sym

  prop-null-empty : Set.null {a} Set.empty ≡ True
  prop-null-empty = primEraseEquality Set.prop-null-empty

  prop-null-insert : ⦃ _ : IsLawfulEq a ⦄
    → (x : a) (s : Set a)
    → Set.null (Set.insert x s) ≡ False
  prop-null-insert x s with Set.null (Set.insert x s) in eq
  ... | False = refl
  ... | True  =
          trans (sym (cong (_|| Set.member x s) (eqReflexivity x)))
          (trans (sym (prop-member-insert x x s))
          (trans (cong (Set.member x) (prop-null→empty _ eq))
          (Set.prop-member-empty x)))

  prop-null-toAscList : {s : Set a}
    → Set.toAscList s ≡ []
    → Set.null s ≡ True
  prop-null-toAscList {s} eq = prop-member-null s λ x →
    trans (sym (prop-member-toAscList x s)) (cong (elem x) eq)

  prop-null-union-left : {s1 s2 : Set a}
    → Set.null (Set.union s1 s2) ≡ True
    → Set.null s1 ≡ True
  prop-null-union-left eq = prop-member-null _ λ x →
    ||-leftFalse (Set.member x _) (Set.member x _)
      (trans (sym (prop-member-union x _ _))
      (trans (cong (Set.member x) (prop-null→empty _ eq))
      (prop-member-empty x)))

  prop-null-union-right : {s1 s2 : Set a}
    → Set.null (Set.union s1 s2) ≡ True
    → Set.null s2 ≡ True
  prop-null-union-right {s1 = s1} {s2} eq
    rewrite prop-union-sym {sa = s1} {sb = s2}
    = prop-null-union-left eq

  prop-null-union' : {s1 s2 : Set a}
    → Set.null s1 ≡ True
    → Set.null s2 ≡ True
    → Set.null (Set.union s1 s2) ≡ True
  prop-null-union' {s1 = s1} {s2} eq1 eq2
    rewrite prop-null→empty s2 eq2
    | prop-union-identity {s = s1}
    = eq1

  prop-null-union : (s1 s2 : Set a)
    → Set.null (Set.union s1 s2) ≡ (Set.null s1 && Set.null s2)
  prop-null-union s1 s2
    with Set.null (Set.union s1 s2) in eq1 | Set.null s1 in eq2 | Set.null s2 in eq3
  ... | False | False | _     = refl
  ... | False | True  | False = refl
  ... | True  | True  | True  = refl
  ... | True  | False | _     = trans (sym (prop-null-union-left eq1)) eq2
  ... | True  | True  | False = trans (sym (prop-null-union-right eq1)) eq3
  ... | False | True  | True  = trans (sym eq1) (prop-null-union' eq2 eq3)

  prop-difference-empty : {sa sb : Set a}
    → Set.difference sa sb ≡ Set.empty
    → ∀ {x}
    → Set.member x sa ≡ True
    → Set.member x sb ≡ True
  prop-difference-empty {sa} {sb} eq1 {x} eq2
    with eq3 ← prop-member-difference x sa sb
    rewrite eq1 | eq2 | prop-member-empty x
    = sym (not-involution False (Set.member x sb) eq3)

  toAscListW' : ⦃ @0 _ : IsLawfulEq a ⦄
    → {@0 s : Set a} (xs : List a)
    → (@0 f : ∀ {x} → elem x xs ≡ True → Set.member x s ≡ True)
    → List (∃ a λ x → Set.member x s ≡ True)
  toAscListW' [] f = []
  toAscListW' (x ∷ xs) f =
    x ⟨ f (cong (_|| elem x xs) (eqReflexivity x)) ⟩ ∷
    toAscListW' xs λ h → f (trans (cong (_ ||_) h) (prop-x-||-True _))
  {-# COMPILE AGDA2HS toAscListW' transparent #-}

  toAscNonEmptyW : ⦃ @0 _ : IsLawfulEq a ⦄
    → (s : Set a)
    → Either
        (Erase (∀ x → Set.member x s ≡ False))
        (NonEmpty (∃ a λ x → Set.member x s ≡ True))
  toAscNonEmptyW s = case Set.toAscList s of λ where
    [] ⦃ eq ⦄ →
      Left (Erased λ x → trans (sym (prop-member-toAscList x s)) (cong (elem x) eq))
    (x ∷ xs) ⦃ eq ⦄ →
      let @0 f : ∀ {y} → elem y (x ∷ xs) ≡ True → Set.member y s ≡ True
          f eq2 = trans (sym (prop-member-toAscList _ s)) (trans (cong (elem _) eq) eq2)
       in Right (x ⟨ f (cong (_|| elem x xs) (eqReflexivity x)) ⟩ NE.∷
                 toAscListW' xs λ eq3 → f (trans (cong (_ ||_) eq3) (prop-x-||-True _)))
  {-# COMPILE AGDA2HS toAscNonEmptyW inline #-}
