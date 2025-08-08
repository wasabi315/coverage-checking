module CoverageCheck.Exhaustiveness where

open import CoverageCheck.Prelude
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Usefulness

-- private
--   variable
--     α β : Ty
--     αs βs : Tys

-- --------------------------------------------------------------------------------
-- -- Exhaustiveness and usefulness

-- -- There is a matching row in P for every list of values
-- Exhaustive : PatMat αs → Set
-- Exhaustive P = ∀ vs → Match P vs

-- -- There is a list of values that does not match any row in P
-- NonExhaustive : PatMat αs → Set
-- NonExhaustive P = ∃[ vs ] ¬ Match P vs

-- -- non-exhaustiveness defined in terms of usefulness:
-- -- P is non-exhaustive if ∙* is useful with respect to P
-- NonExhaustive′ : PatMat αs → Set
-- NonExhaustive′ P = Useful P ∙*

-- -- P is exhaustive if ∙* is not useful with respect to P
-- Exhaustive′ : PatMat αs → Set
-- Exhaustive′ P = ¬ NonExhaustive′ P

-- module _ {P : PatMat αs} where

--   NonExhaustive′→NonExhaustive : NonExhaustive′ P → NonExhaustive P
--   NonExhaustive′→NonExhaustive (vs , ∙*ps⋠vs , _) = vs , contraposition First⇒Any ∙*ps⋠vs

--   NonExhaustive→NonExhaustive′ : NonExhaustive P → NonExhaustive′ P
--   NonExhaustive→NonExhaustive′ (vs , P⋠vs) = vs , ¬First⇒¬Any id P⋠vs , ∙*≼

--   -- The two definitions of non-exhaustiveness are equivalent
--   NonExhaustive′⇔NonExhaustive : NonExhaustive′ P ⇔ NonExhaustive P
--   NonExhaustive′⇔NonExhaustive = mk⇔ NonExhaustive′→NonExhaustive NonExhaustive→NonExhaustive′

--   Exhaustive→Exhaustive′ : Exhaustive P → Exhaustive′ P
--   Exhaustive→Exhaustive′ exh (vs , P⋠vs , _) = P⋠vs (First⇒Any (exh vs))

--   Exhaustive′→Exhaustive : Exhaustive′ P → Exhaustive P
--   Exhaustive′→Exhaustive exh vs with match? P vs
--   ... | yes P≼vs = P≼vs
--   ... | no P⋠vs = contradiction (vs , ¬First⇒¬Any id P⋠vs , ∙*≼) exh

--   -- The two definitions of exhaustiveness are equivalent
--   Exhaustive′⇔Exhaustive : Exhaustive′ P ⇔ Exhaustive P
--   Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

-- --------------------------------------------------------------------------------
-- -- Entrypoint

-- exhaustive? : (P : PatMat αs) → Exhaustive P ⊎ NonExhaustive P
-- exhaustive? P with useful? P ∙*
-- ... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
-- ... | no h = inj₁ (Exhaustive′→Exhaustive h)
