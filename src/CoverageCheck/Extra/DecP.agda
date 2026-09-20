module CoverageCheck.Extra.DecP where

open import Haskell.Prelude
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement

open import CoverageCheck.Data.These
open import CoverageCheck.Extra.Dec
open import CoverageCheck.Extra.Negation

--------------------------------------------------------------------------------

infix 3 tupleDecP

data DecP (a : Type) : Type where
  Yes : (p : a) → DecP a
  No  : (@0 p : ¬ a) → DecP a
{-# COMPILE AGDA2HS DecP deriving Show #-}

mapDecP : ∀ {a b} → (a → b) → @0 (b → a) → DecP a → DecP b
mapDecP f g (Yes p) = Yes (f p)
mapDecP f g (No ¬p) = No (contraposition g ¬p)
{-# COMPILE AGDA2HS mapDecP #-}

ifDecP : {a b : Type} → DecP a → (⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
ifDecP (Yes p) t e = t ⦃ p ⦄
ifDecP (No ¬p) t e = e ⦃ ¬p ⦄
{-# COMPILE AGDA2HS ifDecP #-}

decToDecP : ∀ {@0 a} → Dec a → DecP (Erase a)
decToDecP (False ⟨ ¬a ⟩) = No λ (Erased a) → contradiction a ¬a
decToDecP (True  ⟨ a  ⟩) = Yes (Erased a)
{-# COMPILE AGDA2HS decToDecP #-}

tupleDecP : ∀ {a b} → DecP a → DecP b → DecP (a × b)
syntax tupleDecP a b = a ×-decP b
No ¬p ×-decP _     = No (contraposition fst ¬p)
Yes _ ×-decP No ¬q = No (contraposition snd ¬q)
Yes p ×-decP Yes q = Yes (p , q)
{-# COMPILE AGDA2HS tupleDecP #-}

eitherDecP : ∀ {a b} → DecP a → DecP b → DecP (Either a b)
eitherDecP (Yes p) _       = Yes (Left p)
eitherDecP (No ¬p) (Yes q) = Yes (Right q)
eitherDecP (No ¬p) (No ¬q) = No (either ¬p ¬q)
{-# COMPILE AGDA2HS eitherDecP #-}

theseDecP : ∀ {a b} → DecP a → DecP b → DecP (These a b)
theseDecP (Yes p) (Yes q) = Yes (Both p q)
theseDecP (Yes p) (No ¬q) = Yes (This p)
theseDecP (No ¬p) (Yes q) = Yes (That q)
theseDecP (No ¬p) (No ¬q) = No (these ¬p ¬q (λ _ → ¬q))
{-# COMPILE AGDA2HS theseDecP #-}
