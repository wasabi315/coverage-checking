open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

module CoverageCheck.Usefulness
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    αs : Types

--------------------------------------------------------------------------------

open import CoverageCheck.Usefulness.Algorithm public
open import CoverageCheck.Usefulness.UsefulV as UsefulV public
  hiding (iUsefulnessUsefulV)

module _
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUsefulVTerm : (pss : PatternMatrix αs) (ps : Patterns αs) → DecP (UsefulV pss ps)
  decUsefulVTerm = decUsefulTerm λ ⦃ sig' ⦄ → UsefulV ⦃ sig = sig' ⦄
  {-# COMPILE AGDA2HS decUsefulVTerm inline #-}
