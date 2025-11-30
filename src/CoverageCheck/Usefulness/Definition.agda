open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors
open import CoverageCheck.Usefulness.Algorithm.Properties

module CoverageCheck.Usefulness.Definition
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    αss βss : TyStack
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 αss0 βss0 : TyStack
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Definition of usefulness

module _ ⦃ @0 sig : Signature ⦄ where
  infix 4 SubsumptionStack SubsumptionMatrixStack

  SubsumptionStack : {@0 αss : TyStack} → @0 PatternStack αss → @0 PatternStack αss → Type
  syntax SubsumptionStack pss vss = pss ⊆*ˢ vss
  pss ⊆*ˢ vss = HPointwise (λ ps vs → ps ⊆* vs) pss vss
  {-# COMPILE AGDA2HS SubsumptionStack inline #-}

  SubsumptionMatrixStack : {@0 αss : TyStack} → @0 PatternMatrixStack αss → @0 PatternStack αss → Type
  syntax SubsumptionMatrixStack psss vss = psss ⊆**ˢ vss
  psss ⊆**ˢ vss = Any (λ pss → pss ⊆*ˢ vss) psss
  {-# COMPILE AGDA2HS SubsumptionMatrixStack inline #-}


module _ ⦃ @0 sig : Signature ⦄
  (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0)
  where

  -- ps is useful with respect to P iff there exists a pattern vector qs such that
  --   1. qs is not empty (that is, there exists a value vector vs that matches qs)
  --   2. all rows of P are disjoint from qs
  --   3. ps subsumes qs
  record Useful' : Type where
    no-eta-equality
    pattern
    constructor ⟪_,_,_⟫
    field
      qs       : PatternStack αss0
      @0 P#qs  : P #** qs
      @0 ps⊆qs : ps ⊆*ˢ qs

  open Useful'

  record Useful : Type where
    no-eta-equality
    pattern
    constructor MkUseful
    field
      witnesses : NonEmpty Useful'

  open Useful public

  {-# COMPILE AGDA2HS Useful' unboxed #-}
  {-# COMPILE AGDA2HS Useful  newtype #-}
