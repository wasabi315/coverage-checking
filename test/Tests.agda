{-# OPTIONS --rewriting #-}

module @0 Tests where

open import CoverageCheck
open import CoverageCheck.Prelude
open import CoverageCheck.Data.Set as Set using (Set)
open import CoverageCheck.Data.Set.Rewriting using ()
open import Haskell.Data.List.NonEmpty hiding (cons)

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
_ : decExhaustive Q ≡ Right (Erased (the (∀ vs → FirstMatch vs Q) _))
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
