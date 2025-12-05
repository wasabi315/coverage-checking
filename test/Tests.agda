{-# OPTIONS --rewriting #-}

module @0 Tests where

open import CoverageCheck
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (_∷_)

--------------------------------------------------------------------------------
-- Rewrite rules for Set operations
-- Set and its operations from agda2hs are postulated entities, so we need rewrite
-- rules to enable actual computation in working examples.
-- These rewrite rules may in turn cause the primEraseEquality calls in Prelude to
-- reduce to refl when the sides are definitionally equal, unblocking computation
-- stuck at rewrite clauses.

open import Agda.Builtin.Equality.Rewrite

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

--------------------------------------------------------------------------------
-- Example from the paper

pattern `unit = 'u' ∷ 'n' ∷ 'i' ∷ 't' ∷ []
pattern `list = 'l' ∷ 'i' ∷ 's' ∷ 't' ∷ []
pattern `nil  = 'n' ∷ 'i' ∷ 'l' ∷ []
pattern `one  = 'o' ∷ 'n' ∷ 'e' ∷ []
pattern `cons = 'c' ∷ 'o' ∷ 'n' ∷ 's' ∷ []

pattern ⟨unit⟩ = `unit ⟨ InHere ⟩
pattern ⟨list⟩ = `list ⟨ InThere InHere ⟩
pattern ⟨nil⟩  = `nil ⟨ InHere ⟩
pattern ⟨one⟩  = `one ⟨ InThere InHere ⟩
pattern ⟨cons⟩ = `cons ⟨ InThere (InThere InHere) ⟩

pattern unit      = con ⟨unit⟩ []
pattern nil       = con ⟨nil⟩ []
pattern one x     = con ⟨one⟩ (x ∷ [])
pattern cons x xs = con ⟨cons⟩ (x ∷ xs ∷ [])

instance
  globals : Globals
  globals .dataScope       = `unit ∷# `list ∷# []
  globals .conScope ⟨unit⟩ = `unit ∷# []
  globals .conScope ⟨list⟩ = `nil ∷# `one ∷# `cons ∷# []

  -- type unit = Unit
  unitDef : Dataty ⟨unit⟩
  unitDef .dataCons      = _
  unitDef .isConScope    = refl
  unitDef .argsTy ⟨unit⟩ = []

  -- type list = Nil | One unit | Cons unit list
  listDef : Dataty ⟨list⟩
  listDef .dataCons      = _
  listDef .isConScope    = refl
  listDef .argsTy ⟨nil⟩  = []
  listDef .argsTy ⟨one⟩  = TyData ⟨unit⟩ ∷ []
  listDef .argsTy ⟨cons⟩ = TyData ⟨unit⟩ ∷ TyData ⟨list⟩ ∷ []

  sig : Signature
  sig .dataDefs ⟨unit⟩ = unitDef
  sig .dataDefs ⟨list⟩ = listDef

  nonEmptyAxiom : {α : Ty} → Value α
  nonEmptyAxiom {TyData ⟨unit⟩} = con ⟨unit⟩ []
  nonEmptyAxiom {TyData ⟨list⟩} = con ⟨nil⟩ []


P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ∷ —   ∷ []) ∷
  (—   ∷ nil ∷ []) ∷ []

-- P is non-exhaustive, as witnessed by the following list of patterns
-- Values covered by these witness patterns are proved not to match any row in P
_ : decExhaustive P
  ≡ Left (
      ((cons — —  ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((cons — —  ∷ one —    ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ one —    ∷ []) ⟨ _ ⟩) ∷ [])
_ = refl

-- All rows in P are non-redundant
_ : decAllNonRedundant P ≡ Right _
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ∷ —        ∷ []) ∷
  (—        ∷ nil      ∷ []) ∷
  (one —    ∷ —        ∷ []) ∷
  (—        ∷ one —    ∷ []) ∷
  (cons — — ∷ —        ∷ []) ∷
  (—        ∷ cons — — ∷ []) ∷ []

-- Q is exhaustive, so we obtain a total matching function of type
--   `∀ vs → FirstMatch Q vs`
_ : decExhaustive Q ≡ Right (Erased (the (∀ vs → FirstMatch Q vs) _))
_ = refl

-- The last row of Q is redundant, so we obtain a proof of uselessness for the last row
_ : decAllNonRedundant Q
  ≡ (Left
      $ there
      $ there
      $ there
      $ there
      $ there
      $ Erased
          (the
            (¬ Useful
              ( (nil      ∷ —        ∷ []) ∷
                (—        ∷ nil      ∷ []) ∷
                (one —    ∷ —        ∷ []) ∷
                (—        ∷ one —    ∷ []) ∷
                (cons — — ∷ —        ∷ []) ∷ [])
                (—        ∷ cons — — ∷ []))
            _)
      ∷ [])
_ = refl
