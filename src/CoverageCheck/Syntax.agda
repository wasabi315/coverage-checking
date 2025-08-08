module CoverageCheck.Syntax where

open import CoverageCheck.Prelude

-- infixr 6 _∣_
-- infixr 5 _++ᵥ_ _++ₚ_

-- --------------------------------------------------------------------------------
-- -- Datatypes, values, and patterns

-- record Ty : Set
-- Tys : Set
-- data Val (α : Ty) : Set
-- Vals : Tys → Set

-- -- *Inhabited* datatype
-- record Ty where
--   coinductive
--   field
--     -- The number of constructors
--     numCons : ℕ
--     -- Mapping from constructor to its argument types
--     argsTy : Fin numCons → Tys
--     -- Constructor of the inhabitant
--     inhabCon : Fin numCons
--     -- Constructor arguments of the inhabitant
--     inhabArgs : Vals (argsTy inhabCon)

--   Con : Set
--   Con = Fin numCons

-- open Ty public

-- Tys = List Ty

-- private
--   variable
--     α β : Ty
--     αs βs : Tys

-- -- Value
-- data Val α where
--   con : (c : Con α) → Vals (argsTy α c) → Val α

-- -- (Heterogeneous) list of values
-- Vals = All Val

-- -- The inhabitant
-- inhab : (α : Ty) → Val α
-- inhab α = con (inhabCon α) (inhabArgs α)

-- -- There is an inhabitant for every variant
-- inhabOf : Con α → Val α
-- inhabOf c = con c (tabulateAll λ {α} _ → inhab α)

-- _++ᵥ_ : Vals αs → Vals βs → Vals (αs ++ βs)
-- _++ᵥ_ = ++All⁺

-- data Pat (α : Ty) : Set
-- Pats : Tys → Set

-- -- Pattern
-- data Pat α where
--   -- Wildcard pattern
--   ∙ : Pat α
--   -- Constructor pattern
--   con : (c : Con α) → Pats (argsTy α c) → Pat α
--   -- Or pattern
--   _∣_ : Pat α → Pat α → Pat α

-- -- (Heterogeneous) list of patterns
-- Pats = All Pat

-- -- Matrix of patterns
-- -- Each row corresponds to a clause
-- PatMat = List ∘ Pats

-- -- List of wildcards
-- ∙* : Pats αs
-- ∙* {[]} = []
-- ∙* {_ ∷ _} = ∙ ∷ ∙*

-- _++ₚ_ : Pats αs → Pats βs → Pats (αs ++ βs)
-- _++ₚ_ = ++All⁺
