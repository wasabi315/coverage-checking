open import CoverageCheck.Prelude
open import CoverageCheck.Name
open import CoverageCheck.GlobalScope using (Globals)
open import Data.Set as Set using (Set)

module CoverageCheck.Syntax
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    d : NameData
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Tys and Signatures

data Ty : Type
Tys : Type

data Ty where
  TyData : NameData → Ty

Tys = List Ty

{-# COMPILE AGDA2HS Ty  deriving Show #-}
{-# COMPILE AGDA2HS Tys deriving Show #-}

private
  variable
    α β : Ty
    αs βs : Tys
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys

record Dataty (@0 d : NameData) : Type where
  field
    dataCons        : List Name
    @0 fullDataCons : dataCons ≡ conScope d
    argsTy          : (c : NameCon d) → Tys

  universalNameConSet : Set (NameCon d)
  universalNameConSet =
    subst0 (λ xs → Set (NameIn xs)) fullDataCons (universalNameInSet dataCons)
  {-# COMPILE AGDA2HS universalNameConSet inline #-}

  @0 universalNameConSetUniversal : (c : NameCon d)
    → Set.member c universalNameConSet ≡ True
  universalNameConSetUniversal c rewrite fullDataCons =
    universalNameInSetUniversal (conScope d) c

  @0 universalNameConSetUniversal' : (s : Set (NameCon d))
    → Set.null (Set.difference universalNameConSet s) ≡ True
    → ∀ c → Set.member c s ≡ True
  universalNameConSetUniversal' rewrite fullDataCons =
    universalNameInSetUniversal'

  anyNameCon : (NameCon d → Bool) → Bool
  anyNameCon f = anyNameIn dataCons λ x → f (subst0 NameIn fullDataCons x)
  {-# COMPILE AGDA2HS anyNameCon inline #-}

  decPAnyNameCon : {p : @0 NameCon d → Type}
    → (∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ NameCon d ] p x))
  decPAnyNameCon f = decPAnyNameIn dataCons fullDataCons f
  {-# COMPILE AGDA2HS decPAnyNameCon inline #-}

open Dataty public
{-# COMPILE AGDA2HS Dataty #-}

record Signature : Type where
  field
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
    PCon  : (c : NameCon d0)
      → (ps : Patterns (argsTy (dataDefs sig d0) c))
      → Pattern (TyData d0)
    POr   : (p₁ p₂ : Pattern α0) → Pattern α0

  pattern —         = PWild
  pattern con c ps  = PCon c ps
  pattern _∣_ p₁ p₂ = POr p₁ p₂

  Patterns = All Pattern

  PatternMatrix : (@0 αs : Tys) → Type
  PatternMatrix αs = List (Patterns αs)

  {-# COMPILE AGDA2HS Pattern       deriving (Show, Eq) #-}
  {-# COMPILE AGDA2HS Patterns                          #-}
  {-# COMPILE AGDA2HS PatternMatrix inline              #-}

  pWilds : Patterns αs -- αs is not erasable
  pWilds {αs = []}     = []
  pWilds {αs = α ∷ αs} = — ∷ pWilds
  syntax pWilds = —*
  {-# COMPILE AGDA2HS pWilds #-}

  headPattern : Patterns (α0 ∷ αs0) → Pattern α0
  headPattern (p ∷ _) = p
  {-# COMPILE AGDA2HS headPattern #-}

  tailPatterns : Patterns (α0 ∷ αs0) → Patterns αs0
  tailPatterns (_ ∷ ps) = ps
  {-# COMPILE AGDA2HS tailPatterns #-}

--------------------------------------------------------------------------------

module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  inst  : Pattern α → Value α
  insts : Patterns αs → Values αs

  inst —          = nonEmptyAxiom
  inst (con c ps) = con c (insts ps)
  inst (p ∣ _)    = inst p

  insts []       = []
  insts (p ∷ ps) = inst p ∷ insts ps


module _ ⦃ @0 sig : Signature ⦄ where

  only  : Value α0 → Pattern α0
  onlys : Values αs0 → Patterns αs0

  only (con c vs) = con c (onlys vs)

  onlys [] = []
  onlys (v ∷ vs) = only v ∷ onlys vs

  {-# COMPILE AGDA2HS only #-}
  {-# COMPILE AGDA2HS onlys #-}

--------------------------------------------------------------------------------
-- Non-empty axiom

module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  inhab' : ∀ {d} → Σ[ c ∈ NameCon d ] Values (argsTy (dataDefs sig d) c)
  inhab' {d} = case nonEmptyAxiom {TyData d} of λ where
    (con c vs) → c , vs
  {-# COMPILE AGDA2HS inhab' #-}

  inhabCon : ∀ {d} → NameCon d
  inhabCon = fst inhab'
  {-# COMPILE AGDA2HS inhabCon inline #-}

  inhabArgs : ∀ {d} → Values (argsTy (dataDefs sig d) inhabCon)
  inhabArgs = snd inhab'
  {-# COMPILE AGDA2HS inhabArgs inline #-}

  inhab : ∀ {d} → Value (TyData d)
  inhab = con inhabCon inhabArgs
  {-# COMPILE AGDA2HS inhab #-}

  inhabAt : (c : NameCon d) → Value (TyData d)
  inhabAt c = con c (tabulateValues λ α → nonEmptyAxiom)
  {-# COMPILE AGDA2HS inhabAt #-}