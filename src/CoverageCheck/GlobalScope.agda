module CoverageCheck.GlobalScope where

open import CoverageCheck.Prelude
open import CoverageCheck.Name

--------------------------------------------------------------------------------

record Globals : Set where
  field
    dataScope : List Name
    conScope  : NameIn dataScope → List Name

  NameData : Set
  NameData = NameIn dataScope
  {-# COMPILE AGDA2HS NameData inline #-}

  NameCon : NameData → Set
  NameCon d = NameIn (conScope d)
  {-# COMPILE AGDA2HS NameCon inline #-}

open Globals public
{-# COMPILE AGDA2HS Globals #-}
