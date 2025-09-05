{-# OPTIONS --rewriting #-}

module @0 Example where

open import CoverageCheck
open import Data.Set as Set using (Set)

--------------------------------------------------------------------------------
-- Rewrite rules for Set operations
-- Set and its operations from agda2hs are postulated entities, so we need rewrite
-- rules to enable actual computation in working examples.
-- These rewrite rules in turn cause the primEraseEquality calls in the Prelude to
-- reduce to refl, which is what we want.

open import Agda.Builtin.Equality.Rewrite

postulate
  rewrite-null : ∀ {a : Type} {s}
    → Set.null {a} s ≡ null (Set.toAscList s)
  {-# REWRITE rewrite-null #-}

module _ {A : Type} {{_ : Ord A}} where
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
  globals .dataScope                   = `unit ∷ `list ∷ []
  globals .freshDataScope              = ((λ ()) ∷ []) ∷ [] ∷ []
  globals .conScope      (`unit ⟨ _ ⟩) = `unit ∷ []
  globals .conScope      (`list ⟨ _ ⟩) = `nil ∷ `one ∷ `cons ∷ []
  globals .freshConScope {`unit ⟨ _ ⟩} = [] ∷ []
  globals .freshConScope {`list ⟨ _ ⟩} = ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
  globals .conScope      (_ ⟨ InThere (InThere ()) ⟩)
  globals .freshConScope {_ ⟨ InThere (InThere ()) ⟩}

  -- type unit = Unit
  unitDef : {p : In `unit (dataScope globals)} → Dataty (`unit ⟨ p ⟩)
  unitDef .dataCons             = _
  unitDef .fullDataCons         = refl
  unitDef .argsTy (`unit ⟨ _ ⟩) = []
  unitDef .argsTy (_ ⟨ InThere () ⟩)

  -- type list = Nil | One unit | Cons unit list
  listDef : {p : In `list (dataScope globals)} → Dataty (`list ⟨ p ⟩)
  listDef .dataCons = _
  listDef .fullDataCons = refl
  listDef .argsTy (`nil ⟨ _ ⟩)  = []
  listDef .argsTy (`one ⟨ _ ⟩)  = TyData ⟨unit⟩ ∷ []
  listDef .argsTy (`cons ⟨ _ ⟩) = TyData ⟨unit⟩ ∷ TyData ⟨list⟩ ∷ []
  listDef .argsTy (_ ⟨ InThere (InThere (InThere ())) ⟩)

  sig : Signature
  sig .dataDefs (`unit ⟨ _ ⟩) = unitDef
  sig .dataDefs (`list ⟨ _ ⟩) = listDef
  sig .dataDefs (_ ⟨ InThere (InThere ()) ⟩)

  nonEmptyAxiom : {α : Ty} → Value α
  nonEmptyAxiom {TyData (`unit ⟨ _ ⟩)} = con ⟨unit⟩ []
  nonEmptyAxiom {TyData (`list ⟨ _ ⟩)} = con ⟨nil⟩ []
  nonEmptyAxiom {TyData (_ ⟨ InThere (InThere ()) ⟩)}


P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ∷ —   ∷ []) ∷
  (—   ∷ nil ∷ []) ∷ []

-- P is non-exhaustive, witnessed by the following list of patterns
_ : decNonExhaustive P
  ≡ Right (
      ((cons — —  ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ cons — — ∷ []) ⟨ _ ⟩) ∷
      ((cons — —  ∷ one —    ∷ []) ⟨ _ ⟩) ∷
      ((one —     ∷ one —    ∷ []) ⟨ _ ⟩) ∷ [])
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ∷ —        ∷ []) ∷
  (—        ∷ nil      ∷ []) ∷
  (one —    ∷ —        ∷ []) ∷
  (—        ∷ one —    ∷ []) ∷
  (cons — — ∷ —        ∷ []) ∷
  (—        ∷ cons — — ∷ []) ∷ []

-- Q is exhaustive, so we get a total matching function of type `∀ vs → Match Q vs`
_ : decNonExhaustive Q ≡ Left (Erased (the (∀ vs → Match Q vs) _))
_ = refl
