module CoverageCheck.Extra.Negation where

open import Haskell.Prelude

infix 3 ¬_

--------------------------------------------------------------------------------

¬_ : Type → Type
¬ a = a → ⊥

explode : {a : Type} → @0 ⊥ → a
explode _ = undefined
{-# COMPILE AGDA2HS explode inline #-}

contradiction : {a b : Type} → a → @0 ¬ a → b
contradiction a ¬a = explode (¬a a)
{-# COMPILE AGDA2HS contradiction inline #-}

contraposition : {a b : Type} → (a → b) → (¬ b → ¬ a)
contraposition f g = g ∘ f
