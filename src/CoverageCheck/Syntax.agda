open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty)

module CoverageCheck.Syntax
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    d : NameData
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Types and Signatures

-- We only have datatypes in the type system at the moment
-- TODO: Add other types including integers, functions, and type variables
data Ty : Type where
  TyData : NameData → Ty

{-# COMPILE AGDA2HS Ty deriving Show #-}

Tys : Type
Tys = List Ty

{-# COMPILE AGDA2HS Tys #-}

private
  variable
    α β : Ty
    αs βs : Tys
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys

-- Datatype definition
record Dataty (@0 d : NameData) : Type where
  no-eta-equality
  field
    -- The types of the arguments of each constructor
    argsTy : (c : NameCon d) → Tys
    -- Where we actually store the constructor names for Haskell side
    -- The global scope is truly for Agda side
    dataCons : Scope
    -- dataCons aligns with the global scope
    @0 isConScope : dataCons ≡ conScope d

  -- The complete set of constructor names of this datatype
  nameConSet : Set (NameCon d)
  nameConSet =
    subst0 (λ xs → Set (NameIn xs)) isConScope (nameInSet dataCons)
  {-# COMPILE AGDA2HS nameConSet inline #-}

  -- nameConSet is universal
  @0 nameConSet-universal : (c : NameCon d)
    → Set.member c nameConSet ≡ True
  nameConSet-universal c rewrite isConScope =
    nameInSet-universal (conScope d) c

  -- Any constructor name satisfies a given predicate?
  anyNameCon : (NameCon d → Bool) → Bool
  anyNameCon f = anyNameIn dataCons λ x → f (subst0 NameIn isConScope x)
  {-# COMPILE AGDA2HS anyNameCon inline #-}

  -- Evidence-producing version of anyNameCon
  decPAnyNameCon : {p : @0 NameCon d → Type}
    → (∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ NameCon d ] p x))
  decPAnyNameCon = decPAnyNameIn dataCons isConScope
  {-# COMPILE AGDA2HS decPAnyNameCon inline #-}

open Dataty public
{-# COMPILE AGDA2HS Dataty #-}

record Signature : Type where
  no-eta-equality
  field
    -- The definition of each datatype
    dataDefs : (d : NameData) → Dataty d

open Signature public
{-# COMPILE AGDA2HS Signature newtype #-}

tyData-injective : {d d' : NameData} → TyData d ≡ TyData d' → d ≡ d'
tyData-injective refl = refl

--------------------------------------------------------------------------------
-- Values and Patterns

module _ ⦃ @0 sig : Signature ⦄ where
  infixr 6 _∣_

  data Value : (@0 α : Ty) → Type
  Values : (@0 αs : Tys) → Type

  data Value where
    -- Constructor name and values of the corresponding argument types
    VCon : (c : NameCon d0)
      → (vs : Values (argsTy (dataDefs sig d0) c))
      → Value (TyData d0)

  pattern con c vs = VCon c vs

  Values = All Value

  {-# COMPILE AGDA2HS Value  deriving (Show, Eq) #-}
  {-# COMPILE AGDA2HS Values #-}

  tabulateValues : (∀ α → Value α) → Values αs
  tabulateValues {[]}     f = []
  tabulateValues {α ∷ αs} f = f α ∷ tabulateValues f
  {-# COMPILE AGDA2HS tabulateValues #-}

  data Pattern  : (@0 α : Ty) → Type
  Patterns : (@0 αs : Tys) → Type

  data Pattern where
    PWild : Pattern α0
    PCon : (c : NameCon d0)
      → (ps : Patterns (argsTy (dataDefs sig d0) c))
      → Pattern (TyData d0)
    POr : (p₁ p₂ : Pattern α0) → Pattern α0

  pattern —         = PWild
  pattern con c ps  = PCon c ps
  pattern _∣_ p₁ p₂ = POr p₁ p₂

  Patterns = All Pattern

  -- A matrix of patterns
  -- Each row corresponds to a clause
  PatternMatrix : (@0 αs : Tys) → Type
  PatternMatrix αs = List (Patterns αs)

  {-# COMPILE AGDA2HS Pattern       deriving (Show, Eq) #-}
  {-# COMPILE AGDA2HS Patterns                          #-}
  {-# COMPILE AGDA2HS PatternMatrix inline              #-}

  -- A list of wildcards
  pWilds : Patterns αs
  pWilds {αs = []}     = []
  pWilds {αs = α ∷ αs} = — ∷ pWilds
  syntax pWilds = —*
  {-# COMPILE AGDA2HS pWilds #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄ where

  -- A pattern that matches only a single value
  only  : Value α0 → Pattern α0
  onlys : Values αs0 → Patterns αs0

  only (con c vs) = con c (onlys vs)

  onlys [] = []
  onlys (v ∷ vs) = only v ∷ onlys vs

  {-# COMPILE AGDA2HS only #-}
  {-# COMPILE AGDA2HS onlys #-}

--------------------------------------------------------------------------------
-- Non-empty axiom

-- The algorithm we are formalizing assumes that each type has at least one value.
-- We currently formulate the axiom by the function taking a type and returning
-- some value of that type.
--
-- We are not sure if this is the correct way though.
-- The axiom tells us that each type is well-founded.
-- This would mean that our formalization does not handle a class of datatypes
-- that are not well-founded, e.g.
--
--   type infinite = Infinite of infinite
--
-- TODO: Better way to formulate the axiom?

module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  -- Example constructor name of the datatype d
  exampleCon : ∀ {d} → NameCon d
  exampleCon {d} = case nonEmptyAxiom {TyData d} of λ where (con c _) → c

  -- Example value that matches a pattern
  exampleFor  : Pattern α → Value α
  examplesFor : Patterns αs → Values αs

  exampleFor —          = nonEmptyAxiom
  exampleFor (con c ps) = con c (examplesFor ps)
  exampleFor (p ∣ _)    = exampleFor p

  examplesFor []       = []
  examplesFor (p ∷ ps) = exampleFor p ∷ examplesFor ps
