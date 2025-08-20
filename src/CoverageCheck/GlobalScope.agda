module CoverageCheck.GlobalScope where

open import CoverageCheck.Prelude
open import CoverageCheck.Name

--------------------------------------------------------------------------------

record Globals : Type where
  field
    dataScope : List Name
    conScope : NameIn dataScope → List Name
    ⦃ freshDataScope ⦄ : Fresh dataScope
    ⦃ freshConScope  ⦄ : ∀ {d} → Fresh (conScope d)

  NameData : Type
  NameData = NameIn dataScope
  {-# COMPILE AGDA2HS NameData inline #-}

  NameCon : NameData → Type
  NameCon d = NameIn (conScope d)
  {-# COMPILE AGDA2HS NameCon inline #-}

open Globals public
