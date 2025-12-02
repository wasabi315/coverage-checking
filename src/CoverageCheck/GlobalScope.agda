module CoverageCheck.GlobalScope where

open import CoverageCheck.Prelude
open import CoverageCheck.Name

--------------------------------------------------------------------------------

record Globals : Type where
  field
    dataScope : Scope
    conScope  : NameIn dataScope → Scope

  NameData : Type
  NameData = NameIn dataScope
  {-# COMPILE AGDA2HS NameData inline #-}

  NameCon : NameData → Type
  NameCon d = NameIn (conScope d)
  {-# COMPILE AGDA2HS NameCon inline #-}

open Globals public
