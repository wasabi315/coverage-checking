open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)

module CoverageCheck.Syntax
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    d : NameData
    @0 d0 : NameData

infixr 5 _◂_ appendTypes

--------------------------------------------------------------------------------
-- Types and Signatures

data Type  : Set
Types : Set

data Type where
  TyData : NameData → Type

Types = List Type

pattern ⌈⌉       = []
pattern _◂_ α αs = α ∷ αs

{-# COMPILE AGDA2HS Type  deriving Show #-}
{-# COMPILE AGDA2HS Types deriving Show #-}

appendTypes : Types → Types → Types
appendTypes = _++_
syntax appendTypes αs βs = αs ◂◂ βs
{-# COMPILE AGDA2HS appendTypes inline #-}

private
  variable
    α β : Type
    αs βs : Types
    @0 α0 β0 : Type
    @0 αs0 βs0 : Types

record Datatype (@0 d : NameData) : Set where
  field
    dataCons            : List Name
    @0 ⦃ fullDataCons ⦄ : dataCons ≡ conScope d
    argsTy              : (c : NameCon d) → Types

  allNameCon : (NameCon d → Bool) → Bool
  allNameCon f = allNameIn dataCons λ x → f (subst0 NameIn fullDataCons x)
  {-# COMPILE AGDA2HS allNameCon inline #-}

  decAllNameCon : {@0 p : NameCon d → Set}
    → ((x : NameCon d) → Dec (p x))
    → Either (Erase (∀ x → p x)) (∃[ x ∈ NameCon d ] ¬ p x)
  decAllNameCon f = decAllNameIn dataCons fullDataCons f
  {-# COMPILE AGDA2HS decAllNameCon inline #-}

  anyNameCon : (NameCon d → Bool) → Bool
  anyNameCon f = anyNameIn dataCons λ x → f (subst0 NameIn fullDataCons x)
  {-# COMPILE AGDA2HS anyNameCon inline #-}

  decAnyNameCon : {@0 p : NameCon d → Set}
    → (∀ x → Dec (p x))
    → Dec (∃[ x ∈ NameCon d ] p x)
  decAnyNameCon f = decAnyNameIn dataCons fullDataCons f
  {-# COMPILE AGDA2HS decAnyNameCon inline #-}

  decPAnyNameCon : {p : @0 NameCon d → Set}
    → (∀ x → DecP (p x))
    → DecP (Σ[ x ∈ NameCon d ] p x)
  decPAnyNameCon f = decPAnyNameIn dataCons fullDataCons f
  {-# COMPILE AGDA2HS decPAnyNameCon inline #-}

open Datatype public
{-# COMPILE AGDA2HS Datatype #-}

record Signature : Set where
  field
    dataDefs : (d : NameData) → Datatype d

open Signature public
{-# COMPILE AGDA2HS Signature newtype #-}

tyData-injective : {d d' : NameData} → TyData d ≡ TyData d' → d ≡ d'
tyData-injective refl = refl

--------------------------------------------------------------------------------
-- Values and Patterns

module _ ⦃ @0 sig : Signature ⦄ where
  infixr 6 _∣_
  infixr 5 _◂_ appendValues appendPatterns

  data Value  : (@0 α : Type) → Set
  data Values : (@0 αs : Types) → Set

  data Value where
    VCon : (c : NameCon d0)
      → (vs : Values (argsTy (dataDefs sig d0) c))
      → Value (TyData d0)

  pattern con c vs = VCon c vs

  data Values where
    VNil  : Values ⌈⌉
    VCons : (v : Value α0) (vs : Values αs0) → Values (α0 ◂ αs0)

  pattern ⌈⌉         = VNil
  pattern _◂_ v vs   = VCons v vs

  {-# COMPILE AGDA2HS Value  deriving Show #-}
  {-# COMPILE AGDA2HS Values deriving Show #-}

  appendValues : Values αs0 → Values βs0 → Values (αs0 ◂◂ βs0)
  appendValues ⌈⌉       vs = vs
  appendValues (u ◂ us) vs = u ◂ appendValues us vs
  syntax appendValues us vs = us ◂◂ᵛ vs
  {-# COMPILE AGDA2HS appendValues #-}

  tabulateValues : (∀ α → Value α) → Values αs
  tabulateValues {⌈⌉}     f = ⌈⌉
  tabulateValues {α ◂ αs} f = f α ◂ tabulateValues f
  {-# COMPILE AGDA2HS tabulateValues #-}

  data Pattern  : (@0 α : Type) → Set
  data Patterns : (@0 αs : Types) → Set

  data Pattern where
    PWild : Pattern α0
    PCon  : (c : NameCon d0)
      → (ps : Patterns (argsTy (dataDefs sig d0) c))
      → Pattern (TyData d0)
    POr   : (p₁ p₂ : Pattern α0) → Pattern α0

  pattern —         = PWild
  pattern con c ps  = PCon c ps
  pattern _∣_ p₁ p₂ = POr p₁ p₂

  data Patterns where
    PNil  : Patterns ⌈⌉
    PCons : (p : Pattern α0) (ps : Patterns αs0) → Patterns (α0 ◂ αs0)

  pattern ⌈⌉         = PNil
  pattern _◂_ p ps   = PCons p ps

  PatternMatrix : (@0 αs : Types) → Set
  PatternMatrix αs = List (Patterns αs)

  {-# COMPILE AGDA2HS Pattern       deriving Show #-}
  {-# COMPILE AGDA2HS Patterns      deriving Show #-}
  {-# COMPILE AGDA2HS PatternMatrix inline #-}

  pWilds : Patterns αs -- αs is not erasable
  pWilds {αs = ⌈⌉}    = ⌈⌉
  pWilds {αs = α ◂ αs} = — ◂ pWilds
  syntax pWilds = —*
  {-# COMPILE AGDA2HS pWilds #-}

  headPattern : Patterns (α0 ◂ αs0) → Pattern α0
  headPattern (p ◂ _) = p
  {-# COMPILE AGDA2HS headPattern #-}

  tailPatterns : Patterns (α0 ◂ αs0) → Patterns αs0
  tailPatterns (_ ◂ ps) = ps
  {-# COMPILE AGDA2HS tailPatterns #-}

  appendPatterns : Patterns αs0 → Patterns βs0 → Patterns (αs0 ◂◂ βs0)
  appendPatterns ⌈⌉       qs = qs
  appendPatterns (p ◂ ps) qs = p ◂ appendPatterns ps qs
  syntax appendPatterns ps qs = ps ◂◂ᵖ qs
  {-# COMPILE AGDA2HS appendPatterns #-}
