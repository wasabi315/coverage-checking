{-# OPTIONS --rewriting #-}

module @0 CoverageCheck.Data.Set.Rewriting where

open import Agda.Builtin.Equality.Rewrite

open import Haskell.Prelude
open import CoverageCheck.Data.Set as Set using (Set)

--------------------------------------------------------------------------------
-- Rewrite rules for Set operations
-- Set, its operations, and properties from agda2hs are postulated entities, so we need rewrite
-- rules to enable computation in working examples.
-- These rewrite rules may in turn cause primEraseEquality to reduce when
-- the sides are definitionally equal, unblocking computations
-- stuck at rewrite clauses.

postulate
  rewrite-null : ∀ {a : Type} {s}
    → Set.null {a} s ≡ null (Set.toAscList s)
  {-# REWRITE rewrite-null #-}

module _ {A : Type} ⦃ _ : Ord A ⦄ where
  open import Haskell.Prim.Ord using (_<_)

  -- PRE: xs is sorted and unique
  insert : A → List A → List A
  insert x []           = x ∷ []
  insert x xs@(y ∷ xs') =
    if x < y then x ∷ xs
    else if x == y then xs
    else y ∷ insert x xs'

  -- PRE: xs and ys are sorted and unique
  union : List A → List A → List A
  union []           ys           = ys
  union xs           []           = xs
  union xs@(x ∷ xs') ys@(y ∷ ys') =
    if x < y then x ∷ union xs' ys
    else if x == y then x ∷ union xs' ys'
    else y ∷ union xs ys'

  -- PRE: xs and ys are sorted and unique
  difference : List A → List A → List A
  difference []       ys           = []
  difference xs       []           = xs
  difference (x ∷ xs) ys@(y ∷ ys') =
    if x < y then x ∷ difference xs ys
    else if x == y then difference xs ys'
    else x ∷ difference xs ys'

  nubOrd : List A → List A
  nubOrd [] = []
  nubOrd (x ∷ xs) = insert x (nubOrd xs)


module _ {a : Type} ⦃ _ : Ord a ⦄ where

  postulate
    rewrite-member : ∀ {x s} → Set.member {a} x s ≡ elem x (Set.toAscList s)
    {-# REWRITE rewrite-member #-}

    rewrite-empty : Set.toAscList {a} Set.empty ≡ []
    {-# REWRITE rewrite-empty #-}

    rewrite-fromList : ∀ {xs}
      → Set.toAscList {a} (Set.fromList xs) ≡ nubOrd xs
    {-# REWRITE rewrite-fromList #-}

    rewrite-insert : ∀ {x xs}
      → Set.toAscList {a} (Set.insert x xs) ≡ insert x (Set.toAscList xs)
    {-# REWRITE rewrite-insert #-}

    rewrite-union : ∀ {xs ys}
      → Set.toAscList {a} (Set.union xs ys) ≡ union (Set.toAscList xs) (Set.toAscList ys)
    {-# REWRITE rewrite-union #-}

    rewrite-difference : ∀ {xs ys}
      → Set.toAscList {a} (Set.difference xs ys) ≡ difference (Set.toAscList xs) (Set.toAscList ys)
    {-# REWRITE rewrite-difference #-}
