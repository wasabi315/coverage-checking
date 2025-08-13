open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)

module CoverageCheck.Syntax
  {{@0 globals : Globals}}
  where

private open module @0 G = Globals globals

infixr 5 _◂_ appendTypes

--------------------------------------------------------------------------------
-- Types and Signatures

data Type  : Set
data Types : Set

data Type where
  TyData : NameData → Type

data Types where
  TNil  : Types
  TCons : Type → Types → Types

pattern ⌈⌉       = TNil
pattern _◂_ α αs = TCons α αs

{-# COMPILE AGDA2HS Type  deriving Show #-}
{-# COMPILE AGDA2HS Types deriving Show #-}

appendTypes : Types → Types → Types
appendTypes ⌈⌉       βs = βs
appendTypes (α ◂ αs) βs = α ◂ appendTypes αs βs
syntax appendTypes αs βs = αs ◂◂ βs
{-# COMPILE AGDA2HS appendTypes #-}

record Datatype (@0 d : NameData) : Set where
  field
    dataCons : Rezz (conScope d)
    argsTy   : (c : NameCon d) → Types

open Datatype public
{-# COMPILE AGDA2HS Datatype #-}

allNameCon : {@0 d : NameData} → Datatype d → (NameCon d → Bool) → Bool
allNameCon dty f =
  let xs ⟨ h ⟩ = dataCons dty in
  allNameIn xs λ x → f (subst0 NameIn (sym h) x)
{-# COMPILE AGDA2HS allNameCon #-}

decAllNameCon : {@0 d : NameData} (dty : Datatype d) {@0 p : NameCon d → Set}
  → ((x : NameCon d) → Dec (p x))
  → Either (Erase (∀ x → p x)) (Erase (∃[ x ∈ _ ] ¬ p x))
decAllNameCon dty f =
  let xs ⟨ h ⟩ = dataCons dty in
  decAllNameIn xs h f
{-# COMPILE AGDA2HS decAllNameCon #-}

anyNameCon : {@0 d : NameData} → Datatype d → (NameCon d → Bool) → Bool
anyNameCon dty f =
  let xs ⟨ h ⟩ = dataCons dty in
  anyNameIn xs λ x → f (subst0 NameIn (sym h) x)
{-# COMPILE AGDA2HS anyNameCon #-}

decAnyNameCon : {@0 d : NameData} (dty : Datatype d) {@0 p : NameCon d → Set}
  → ((x : NameCon d) → Dec (p x))
  → Dec (∃[ x ∈ NameCon d ] p x)
decAnyNameCon dty f =
  let xs ⟨ h ⟩ = dataCons dty in
  decAnyNameIn xs h f
{-# COMPILE AGDA2HS decAnyNameCon #-}

decPAnyNameCon : {@0 d : NameData} (dty : Datatype d) {p : @0 NameCon d → Set}
  → ((x : NameCon d) → DecP (p x))
  → DecP (Σ[ x ∈ NameCon d ] p x)
decPAnyNameCon dty f =
  let xs ⟨ h ⟩ = dataCons dty in
  decPAnyNameIn xs h f
{-# COMPILE AGDA2HS decPAnyNameCon #-}

record Signature : Set where
  field
    dataDefs : (d : NameData) → Datatype d

open Signature public
{-# COMPILE AGDA2HS Signature newtype #-}

tyData-injective : {d d' : NameData} → TyData d ≡ TyData d' → d ≡ d'
tyData-injective refl = refl

--------------------------------------------------------------------------------
-- Values and Patterns

module _ {{@0 sig : Signature}} where
  infixr 6 _∣_
  infixr 5 _◂_ appendValues appendPatterns

  data Value  : (@0 α : Type) → Set
  data Values : (@0 αs : Types) → Set

  data Value where
    VCon : {@0 d : NameData} (c : NameCon d)
      → (vs : Values (argsTy (dataDefs sig d) c))
      → Value (TyData d)

  pattern con c vs = VCon c vs

  data Values where
    VNil  : Values ⌈⌉
    VCons : ∀ {@0 α αs} (v : Value α) (vs : Values αs) → Values (α ◂ αs)

  pattern ⌈⌉         = VNil
  pattern _◂_ v vs   = VCons v vs

  {-# COMPILE AGDA2HS Value  deriving Show #-}
  {-# COMPILE AGDA2HS Values deriving Show #-}

  appendValues : ∀ {@0 αs βs} → Values αs → Values βs → Values (αs ◂◂ βs)
  appendValues ⌈⌉       vs = vs
  appendValues (u ◂ us) vs = u ◂ appendValues us vs
  syntax appendValues us vs = us ◂◂ᵛ vs
  {-# COMPILE AGDA2HS appendValues #-}

  data Pattern  : (@0 α : Type) → Set
  data Patterns : (@0 αs : Types) → Set

  data Pattern where
    PWild : ∀ {@0 α} → Pattern α
    PCon  : {@0 d : NameData} (c : NameCon d)
      → (ps : Patterns (argsTy (dataDefs sig d) c))
      → Pattern (TyData d)
    POr   : ∀ {@0 α} (p₁ p₂ : Pattern α) → Pattern α

  pattern —         = PWild
  pattern con c ps  = PCon c ps
  pattern _∣_ p₁ p₂ = POr p₁ p₂

  data Patterns where
    PNil  : Patterns ⌈⌉
    PCons : ∀ {@0 α αs} (p : Pattern α) (ps : Patterns αs) → Patterns (α ◂ αs)

  pattern ⌈⌉         = PNil
  pattern _◂_ p ps   = PCons p ps

  PatternMatrix : (@0 αs : Types) → Set
  PatternMatrix αs = List (Patterns αs)

  {-# COMPILE AGDA2HS Pattern       deriving Show #-}
  {-# COMPILE AGDA2HS Patterns      deriving Show #-}
  {-# COMPILE AGDA2HS PatternMatrix inline #-}

  pWilds : ∀ {αs} → Patterns αs -- αs is not erasable
  pWilds {αs = ⌈⌉}    = ⌈⌉
  pWilds {αs = α ◂ αs} = — ◂ pWilds
  syntax pWilds = —*
  {-# COMPILE AGDA2HS pWilds #-}

  headPattern : ∀ {@0 α αs} → Patterns (α ◂ αs) → Pattern α
  headPattern (p ◂ _) = p
  {-# COMPILE AGDA2HS headPattern #-}

  tailPatterns : ∀ {@0 α αs} → Patterns (α ◂ αs) → Patterns αs
  tailPatterns (_ ◂ ps) = ps
  {-# COMPILE AGDA2HS tailPatterns #-}

  appendPatterns : ∀ {@0 αs βs} → Patterns αs → Patterns βs → Patterns (αs ◂◂ βs)
  appendPatterns ⌈⌉       qs = qs
  appendPatterns (p ◂ ps) qs = p ◂ appendPatterns ps qs
  syntax appendPatterns ps qs = ps ◂◂ᵖ qs
  {-# COMPILE AGDA2HS appendPatterns #-}
