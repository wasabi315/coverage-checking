open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

module CoverageCheck.Usefulness
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

--------------------------------------------------------------------------------

open import CoverageCheck.Usefulness.Algorithm public
open import CoverageCheck.Usefulness.Usefulness1 public
