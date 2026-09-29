open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  (+-identityʳ; +-assoc; +-suc; ≤-refl; ≤-reflexive; module ≤-Reasoning;
  +-mono-≤; +-monoˡ-≤; +-mono-<-≤; +-mono-≤-<; n≤1+n; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum as Sum using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded as WellFounded using (WellFounded)
open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)
open import Tactic.Cong using (cong!; ⌞_⌟)

open import CoverageCheck.Prelude hiding (Σ-syntax; _×_; _<_) renaming (_,_ to infixr 4 _,_)
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Name

open import CoverageCheck.Usefulness.Algorithm.Types hiding (_,_,_)
open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors

module @0 CoverageCheck.Usefulness.Algorithm.Termination
  ⦃ globals : Globals ⦄
  ⦃ sig : Signature ⦄
  where

private open module G = Globals globals

open ≤-Reasoning

private
  variable
    α : Ty
    αs βs : Tys
    αss βss : TyStack
    d : NameData

--------------------------------------------------------------------------------
-- Termination measures

--
-- The algorithm is driven by the pattern sequence argument, so one may think
-- we can prove termination with a measure on the argument. Unfortunately, it
-- is impossible. The culprit is the wildcard case with a complete signature set,
-- where we expand a wildcard pattern into multiple wildcard patterns according
-- to the constructor definition. This means that the plain size grows arbitrarily!
-- And the number of such steps is bounded only by the pattern matrix argument.
--
-- Therefore we need a measure on the pattern matrix argument that never
-- increases and strictly decreases in the evil case, so that two
-- form a lexicographic measure. This formalisation adopts the number of
-- constructor patterns for that. Note that we count it after expanding
-- or-patterns because the operations on matrices expand or-patterns into multiple clauses.
--
--   +---------------------------+-------------+-----------+
--   |    step    \   size       |  ∣ psmat ∣  |  ∥ pss ∥  |
--   +---------------------------+-------------+-----------+
--   | tail case                 |      =      |     <     |
--   | con case                  |      ≤      |     <     |
--   | wildcard case (missing)   |      ≤      |     <     |
--   | wildcard case (complete)  |      <      |     ?     |
--   | or case                   |      =      |     <     |
--   +---------------------------+-------------+-----------+
--

record ConCnt (A : Type) : Type₁ where
  -- the number of constructor patterns after expanding or-patterns
  field
    Ret : Type
    ∣_∣ : A → Ret

record NodeCnt (A : Type) : Type where
  -- plain structural size
  field ∥_∥ : A → Nat

open ConCnt  ⦃ ... ⦄
open NodeCnt ⦃ ... ⦄

instance

  conCntPatterns : ConCnt (Patterns αs)
  Ret ⦃ conCntPatterns ⦄ = Nat → Nat
  ∣_∣ ⦃ conCntPatterns ⦄ []              k = k
  ∣_∣ ⦃ conCntPatterns ⦄ (—        ∷ ps) k = ∣ ps ∣ k
  ∣_∣ ⦃ conCntPatterns ⦄ (con c rs ∷ ps) k = suc (∣ rs ∣ (∣ ps ∣ k))
  ∣_∣ ⦃ conCntPatterns ⦄ (r₁ ∣ r₂  ∷ ps) k = ∣ r₁ ∷ ps ∣ k + ∣ r₂ ∷ ps ∣ k
  -- actually we just need to duplicate the count for the remaining patterns 'k'

  conCntPatternStack : ConCnt (PatternStack αss)
  Ret ⦃ conCntPatternStack ⦄ = Nat → Nat
  ∣_∣ ⦃ conCntPatternStack ⦄ []         k = k
  ∣_∣ ⦃ conCntPatternStack ⦄ (ps ∷ pss) k = ∣ ps ∣ (∣ pss ∣ k)

  conCntPatternStackMatrix : ConCnt (PatternStackMatrix αss)
  Ret ⦃ conCntPatternStackMatrix ⦄ = Nat
  ∣_∣ ⦃ conCntPatternStackMatrix ⦄ []            = 0
  ∣_∣ ⦃ conCntPatternStackMatrix ⦄ (pss ∷ psmat) = ∣ pss ∣ 0 + ∣ psmat ∣

  nodeCntPattern  : NodeCnt (Pattern α)
  nodeCntPatterns : NodeCnt (Patterns αs)
  ∥_∥ ⦃ nodeCntPattern  ⦄ —          = 1
  ∥_∥ ⦃ nodeCntPattern  ⦄ (con c ps) = suc (∥ ps ∥)
  ∥_∥ ⦃ nodeCntPattern  ⦄ (p ∣ q)    = suc (∥ p ∥ + ∥ q ∥)
  ∥_∥ ⦃ nodeCntPatterns ⦄ []         = 1
  ∥_∥ ⦃ nodeCntPatterns ⦄ (p ∷ ps)   = suc (∥ p ∥ + ∥ ps ∥)

  nodeCntPatternStack : NodeCnt (PatternStack αss)
  ∥_∥ ⦃ nodeCntPatternStack ⦄ []         = 1
  ∥_∥ ⦃ nodeCntPatternStack ⦄ (ps ∷ pss) = suc (∥ ps ∥ + ∥ pss ∥)


Input : Type
Input = Σ[ αss ∈ _ ] PatternStackMatrix αss × PatternStack αss

size : Input → Nat × Nat
size (_ , psmat , pss) = ∣ psmat ∣ , ∥ pss ∥

_⊏_ : Input → Input → Type
_⊏_ = ×-Lex _≡_ _<_ _<_ on size

-- _⊏_ is well-founded
⊏-wellFounded : WellFounded _⊏_
⊏-wellFounded = on-wellFounded size (×-wellFounded <-wellFounded <-wellFounded)

open WellFounded.All ⊏-wellFounded renaming (wfRec to ⊏-rec)

--------------------------------------------------------------------------------

∣∣-homo-++ : (psmat psmat' : PatternStackMatrix αss)
  → ∣ psmat ++ psmat' ∣ ≡ ∣ psmat ∣ + ∣ psmat' ∣
∣∣-homo-++ []            psmat' = refl
∣∣-homo-++ (pss ∷ psmat) psmat' =
  trans
    (cong (∣ pss ∣ 0 +_) (∣∣-homo-++ psmat psmat'))
    (sym (+-assoc (∣ pss ∣ 0) _ _))

--------------------------------------------------------------------------------
-- Tail case

tail-≡ : (psmat : PatternStackMatrix ([] ∷ αss))
  → ∣ map tailAll psmat ∣ ≡ ∣ psmat ∣
tail-≡ []                   = refl
tail-≡ (([] ∷ pss) ∷ psmat) = cong (_ +_) (tail-≡ psmat)

tail-⊏ : (psmat : PatternStackMatrix ([] ∷ αss)) (pss : PatternStack αss)
  → (_ , map tailAll psmat , pss) ⊏ (_ , psmat , [] ∷ pss)
tail-⊏ psmat pss = inj₂ (tail-≡ psmat , n≤1+n _)

--------------------------------------------------------------------------------
-- Constructor pattern case

∣—*∣ : ∀ αs {n : Nat} → ∣ —* {αs} ∣ n ≡ n
∣—*∣ []       = refl
∣—*∣ (α ∷ αs) = ∣—*∣ αs

specializeConCase-≤
  : (c c' : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c'))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → (c≟c' : Dec (c ≡ c'))
  → ∣ specializeConCase c rs ps pss c≟c' ∣ ≤ ∣ (con c' rs ∷ ps) ∷ pss ∣ 0
specializeConCase-≤ c c' rs ps pss (False ⟨ _ ⟩) = z≤n
specializeConCase-≤ c c' rs ps pss (True ⟨ refl ⟩) =
  begin
    ∣ rs ∣ (∣ ps ∣ (∣ pss ∣ 0)) + 0
  ≡⟨ +-identityʳ _ ⟩
    ∣ rs ∣ (∣ ps ∣ (∣ pss ∣ 0))
  ≤⟨ n≤1+n _ ⟩
    suc (∣ rs ∣ (∣ ps ∣ (∣ pss ∣ 0)))
  ∎

specialize'-≤ : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → ∣ specialize' c pss ∣ ≤ ∣ pss ∣ 0
specialize'-≤ {d = d} c ((— ∷ ps) ∷ pss) =
  begin
    ∣ —* {αs = argsTy (dataDefs sig d) c} ∣ (∣ ps ∣ (∣ pss ∣ 0)) + 0
  ≡⟨ +-identityʳ _ ⟩
    ∣ —* {αs = argsTy (dataDefs sig d) c} ∣ (∣ ps ∣ (∣ pss ∣ 0))
  ≡⟨ ∣—*∣ (argsTy (dataDefs sig d) c) ⟩
    ∣ ps ∣ (∣ pss ∣ 0)
  ∎
specialize'-≤ c ((con c' rs ∷ ps) ∷ pss) = specializeConCase-≤ c c' rs ps pss (c ≟ c')
specialize'-≤ c ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    ∣ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∣
  ≡⟨ ∣∣-homo-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) _ ⟩
    ∣ specialize' c ((r₁ ∷ ps) ∷ pss) ∣ + ∣ specialize' c ((r₂ ∷ ps) ∷ pss) ∣
  ≤⟨ +-mono-≤ (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss)) ⟩
    ∣ (r₁ ∷ ps) ∷ pss ∣ 0 + ∣ (r₂ ∷ ps) ∷ pss ∣ 0
  ∎

specialize-≤
  : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → ∣ specialize c psmat ∣ ≤ ∣ psmat ∣
specialize-≤ c [] = ≤-refl
specialize-≤ c (pss ∷ psmat) =
  begin
    ∣ specialize' c pss ++ specialize c psmat ∣
  ≡⟨ ∣∣-homo-++ (specialize' c pss) _ ⟩
    ∣ specialize' c pss ∣ + ∣ specialize c psmat ∣
  ≤⟨ +-mono-≤ (specialize'-≤ c pss) (specialize-≤ c psmat) ⟩
    ∣ pss ∣ 0 + ∣ psmat ∣
  ∎

specialize-≡ : (c : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → ∥ rs ∷ ps ∷ pss ∥ < ∥ (con c rs ∷ ps) ∷ pss ∥
specialize-≡ c rs ps pss =
  begin
    suc (suc (∥ rs ∥ + suc (∥ ps ∥ + ∥ pss ∥)))
  ≡⟨ cong! (+-suc ∥ rs ∥ _) ⟩
    suc (suc (suc ⌞ ∥ rs ∥ + (∥ ps ∥ + ∥ pss ∥) ⌟))
  ≡⟨ cong! (+-assoc ∥ rs ∥ _ _) ⟨
    suc (suc (suc (∥ rs ∥ + ∥ ps ∥ + ∥ pss ∥)))
  ∎

specializeCon-⊏ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (c : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , specialize c psmat , rs ∷ ps ∷ pss) ⊏ (_ , psmat , (con c rs ∷ ps) ∷ pss)
specializeCon-⊏ psmat c rs ps pss =
  Sum.map₂ (_, specialize-≡ c rs ps pss) (m≤n⇒m<n∨m≡n (specialize-≤ c psmat))

--------------------------------------------------------------------------------
-- Wildcard case (missing constructor)

default'-≤ : (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → ∣ default' pss ∣ ≤ ∣ pss ∣ 0
default'-≤ ((— ∷ ps) ∷ pss) = ≤-reflexive (+-identityʳ (∣ ps ∣ (∣ pss ∣ 0)))
default'-≤ ((con _ _ ∷ _) ∷ _) = z≤n
default'-≤ ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    ∣ default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss) ∣
  ≡⟨ ∣∣-homo-++ (default' ((r₁ ∷ ps) ∷ pss)) _ ⟩
    ∣ default' ((r₁ ∷ ps) ∷ pss) ∣ + ∣ default' ((r₂ ∷ ps) ∷ pss) ∣
  ≤⟨ +-mono-≤ (default'-≤ ((r₁ ∷ ps) ∷ pss)) (default'-≤ ((r₂ ∷ ps) ∷ pss)) ⟩
    ∣ (r₁ ∷ ps) ∷ pss ∣ 0 + ∣ (r₂ ∷ ps) ∷ pss ∣ 0
  ∎

default-≤ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → ∣ default_ psmat ∣ ≤ ∣ psmat ∣
default-≤ [] = ≤-refl
default-≤ (pss ∷ psmat) =
  begin
    ∣ default' pss ++ default psmat ∣
  ≡⟨ ∣∣-homo-++ (default' pss) _ ⟩
    ∣ default' pss ∣ + ∣ default psmat ∣
  ≤⟨ +-mono-≤ (default'-≤ pss) (default-≤ psmat) ⟩
    ∣ pss ∣ 0 + ∣ psmat ∣
  ∎

default-⊏ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → (_ , default_ psmat , qs ∷ pss) ⊏ (_ , psmat , (— ∷ qs) ∷ pss)
default-⊏ psmat qs pss = Sum.map₂ (_, n≤1+n _) (m≤n⇒m<n∨m≡n (default-≤ psmat))

--------------------------------------------------------------------------------
-- Wildcard case (complete constructor set)

specializeConCase-<
  : (c c' : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c'))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → (c≟c' : Dec (c ≡ c'))
  → c ≡ c'
  → ∣ specializeConCase c rs ps pss c≟c' ∣ < ∣ (con c' rs ∷ ps) ∷ pss ∣ 0
specializeConCase-< c c' rs ps pss (False ⟨ c≢c' ⟩) c≡c' = contradiction c≡c' c≢c'
specializeConCase-< c c' rs ps pss (True  ⟨ refl ⟩) c≡c' = ≤-reflexive (+-identityʳ _)

specialize'-< : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → c ∈ pss
  → ∣ specialize' c pss ∣ < ∣ pss ∣ 0
specialize'-< c ((con c' rs ∷ ps) ∷ pss) c≡c' = specializeConCase-< c c' rs ps pss (c ≟ c') c≡c'
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Left c∈r₁) =
  begin
    suc ∣ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∣
  ≡⟨ cong! (∣∣-homo-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) _) ⟩
    suc (∣ specialize' c ((r₁ ∷ ps) ∷ pss) ∣ + ∣ specialize' c ((r₂ ∷ ps) ∷ pss) ∣)
  ≤⟨ +-mono-<-≤ (specialize'-< c ((r₁ ∷ ps) ∷ pss) c∈r₁) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss)) ⟩
    ∣ (r₁ ∷ ps) ∷ pss ∣ 0 + ∣ (r₂ ∷ ps) ∷ pss ∣ 0
  ∎
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Right c∈r₂) =
  begin
    suc ∣ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∣
  ≡⟨ cong! (∣∣-homo-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) _) ⟩
    suc (∣ specialize' c ((r₁ ∷ ps) ∷ pss) ∣ + ∣ specialize' c ((r₂ ∷ ps) ∷ pss) ∣)
  ≤⟨ +-mono-≤-< (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-< c ((r₂ ∷ ps) ∷ pss) c∈r₂) ⟩
    ∣ (r₁ ∷ ps) ∷ pss ∣ 0 + ∣ (r₂ ∷ ps) ∷ pss ∣ 0
  ∎

specialize-< : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → c ∈ psmat
  → ∣ specialize c psmat ∣ < ∣ psmat ∣
specialize-< c (pss ∷ psmat) (Here h) =
  begin
    suc ∣ specialize' c pss ++ specialize c psmat ∣
  ≡⟨ cong! (∣∣-homo-++ (specialize' c pss) _) ⟩
    suc (∣ specialize' c pss ∣ + ∣ specialize c psmat ∣)
  ≤⟨ +-mono-<-≤ (specialize'-< c pss h) (specialize-≤ c psmat) ⟩
    ∣ pss ∣ 0 + ∣ psmat ∣
  ∎
specialize-< c (pss ∷ psmat) (There h) =
  begin
    suc ∣ specialize' c pss ++ specialize c psmat ∣
  ≡⟨ cong! (∣∣-homo-++ (specialize' c pss) _) ⟩
    suc (∣ specialize' c pss ∣ + ∣ specialize c psmat ∣)
  ≤⟨ +-mono-≤-< (specialize'-≤ c pss) (specialize-< c psmat h) ⟩
    ∣ pss ∣ 0 + ∣ psmat ∣
  ∎

specializeWild-⊏
  : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → c ∈ psmat
  → (_ , specialize c psmat , —* ∷ qs ∷ pss) ⊏ (_ , psmat , (— ∷ qs) ∷ pss)
specializeWild-⊏ c psmat qs pss h = inj₁ (specialize-< c psmat h)

--------------------------------------------------------------------------------
-- Or-pattern case

or-<ₗ : (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → ∥ (r₁ ∷ ps) ∷ pss ∥ < ∥ ((r₁ ∣ r₂) ∷ ps) ∷ pss ∥
or-<ₗ r₁ r₂ ps pss =
  s≤s $ s≤s $ s≤s $ +-monoˡ-≤ ∥ pss ∥ $ +-monoˡ-≤ ∥ ps ∥ $ m≤m+n ∥ r₁ ∥ ∥ r₂ ∥

or-<ᵣ : (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → ∥ (r₂ ∷ ps) ∷ pss ∥ < ∥ ((r₁ ∣ r₂) ∷ ps) ∷ pss ∥
or-<ᵣ r₁ r₂ ps pss =
  s≤s $ s≤s $ s≤s $ +-monoˡ-≤ ∥ pss ∥ $ +-monoˡ-≤ ∥ ps ∥ $ m≤n+m ∥ r₂ ∥ ∥ r₁ ∥

or-⊏ₗ : (psmat : PatternStackMatrix ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , psmat , (r₁ ∷ ps) ∷ pss) ⊏ (_ , psmat , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
or-⊏ₗ psmat r₁ r₂ ps pss = inj₂ (refl , or-<ₗ r₁ r₂ ps pss)

or-⊏ᵣ : (psmat : PatternStackMatrix ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , psmat , (r₂ ∷ ps) ∷ pss) ⊏ (_ , psmat , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
or-⊏ᵣ psmat r₁ r₂ ps pss = inj₂ (refl , or-<ᵣ r₁ r₂ ps pss)

--------------------------------------------------------------------------------
-- Termination proof

-- Specialized accessibility predicate for usefulness checking algorithm
-- This method by Ana Bove allows separation of termination proof from the algorithm
data UsefulAcc : (psmat : PatternStackMatrix αss) (ps : PatternStack αss) → Type where
  done : {psmat : PatternStackMatrix []} → UsefulAcc psmat []

  tailStep : {psmat : PatternStackMatrix ([] ∷ αss)} {pss : PatternStack αss}
    → UsefulAcc (map tailAll psmat) pss
    → UsefulAcc psmat ([] ∷ pss)

  wildStep : {psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss)}
    → {ps : Patterns αs} {pss : PatternStack αss}
    → UsefulAcc (default_ psmat) (ps ∷ pss)
    → (∀ c → c ∈ psmat → UsefulAcc (specialize c psmat) (—* ∷ ps ∷ pss))
    → UsefulAcc psmat ((— ∷ ps) ∷ pss)

  conStep : {psmat : PatternStackMatrix ((TyData d ∷ βs) ∷ αss)} {c : NameCon d}
    → (let αs = argsTy (dataDefs sig d) c)
    → {rs : Patterns αs} {ps : Patterns βs} {pss : PatternStack αss}
    → UsefulAcc (specialize c psmat) (rs ∷ ps ∷ pss)
    → UsefulAcc psmat ((con c rs ∷ ps) ∷ pss)

  orStep : {psmat : PatternStackMatrix ((α ∷ αs) ∷ αss)}
    → {r₁ r₂ : Pattern α} {ps : Patterns αs} {pss : PatternStack αss}
    → UsefulAcc psmat ((r₁ ∷ ps) ∷ pss)
    → UsefulAcc psmat ((r₂ ∷ ps) ∷ pss)
    → UsefulAcc psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)

-- UsefulAcc can be constructed for any input
∀UsefulAcc : (psmat : PatternStackMatrix αss) (pss : PatternStack αss)
  → UsefulAcc psmat pss
∀UsefulAcc psmat pss =
  ⊏-rec _ (λ (_ , psmat , pss) → UsefulAcc psmat pss)
    (λ where
      (_ , psmat , []) _ →
        done
      (_ , psmat , [] ∷ pss) rec →
        tailStep (rec (tail-⊏ psmat pss))
      (_ , psmat , (con c rs ∷ ps) ∷ pss) rec →
        conStep (rec (specializeCon-⊏ psmat c rs ps pss))
      (_ , psmat , (r₁ ∣ r₂ ∷ ps) ∷ pss) rec →
        orStep
          (rec (or-⊏ₗ psmat r₁ r₂ ps pss))
          (rec (or-⊏ᵣ psmat r₁ r₂ ps pss))
      ((TyData _ ∷ _) ∷ _ , psmat , (— ∷ ps) ∷ pss) rec →
        wildStep
          (rec (default-⊏ psmat ps pss))
          (λ c h → rec (specializeWild-⊏ c psmat ps pss h)))
    (_ , psmat , pss)
