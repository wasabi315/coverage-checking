open import Data.Nat.Base using (_≤_; _<_; s<s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  (+-identityʳ; +-assoc; ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
  n<1+n; 0<1+n; +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded as WellFounded using (WellFounded; Acc; acc)
open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)

open import CoverageCheck.Prelude hiding (Σ-syntax; _×_; _,_; _<_)
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

open import CoverageCheck.Usefulness.Algorithm.Types hiding (_,_)
open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors

module @0 CoverageCheck.Usefulness.Algorithm.Termination
  ⦃ globals : Globals ⦄
  ⦃ sig : Signature ⦄
  where

private open module G = Globals globals

private
  variable
    α : Ty
    αs βs : Tys
    αss : TyStack
    d : NameData

--------------------------------------------------------------------------------
-- Termination measures

-- The algorithm has a complicated recursive structure. In particular, the
-- following details prevent us from using naive pattern size as a measure:
--   1. The specialize and default operations expand or-patterns into multiple clauses
--   2. The specialize operation expands a wildcard pattern into multiple wildcard patterns
-- The measure we use is based on the following idea:
--   a. Calculate the size after expanding all or-patterns (while still counting
--      the number of or-patterns) to overcome the first issue
--   b. Do not count wildcard patterns in the size calculation to overcome the second issue
--   c. The size does not decrease for some steps because of b. To address this,
--      we use a lexicographic order combining other measures that decrease at those steps

∥_∥ : Patterns αs → Nat → Nat
∥ [] ∥ n = n
∥ — ∷ ps ∥ n = ∥ ps ∥ n
∥ con c rs ∷ ps ∥ n = suc (∥ rs ∥ (∥ ps ∥ n))
∥ r₁ ∣ r₂ ∷ ps ∥ n = suc (∥ r₁ ∷ ps ∥ n + ∥ r₂ ∷ ps ∥ n)

∥_∥ˢ' : PatternStack αss → Nat → Nat
∥ [] ∥ˢ' n = n
∥ ps ∷ pss ∥ˢ' n = ∥ ps ∥ (∥ pss ∥ˢ' n)

∥_∥ˢ : PatternStack αss → Nat
∥ pss ∥ˢ = ∥ pss ∥ˢ' 0

∥_∥ˢᵐ : PatternStackMatrix αss → Nat
∥ psmat ∥ˢᵐ = sum (map ∥_∥ˢ psmat)

∥_∥ᵗ : TyStack → Nat
∥ [] ∥ᵗ = 0
∥ αs ∷ αss ∥ᵗ = suc (lengthNat αs + ∥ αss ∥ᵗ)

Input : Type
Input = Σ[ αss ∈ _ ] PatternStackMatrix αss × PatternStack αss

inputSize : Input → Nat × Nat × Nat
inputSize (αss , psmat , ps) = ∥ psmat ∥ˢᵐ , ∥ ps ∥ˢ , ∥ αss ∥ᵗ

-- Lexicographic ordering on Inputs
_⊏_ : Input → Input → Type
_⊏_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_) on inputSize

-- _⊏_ is well-founded
⊏-wellFounded : WellFounded _⊏_
⊏-wellFounded =
  on-wellFounded inputSize
    (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded))

open WellFounded.All ⊏-wellFounded renaming (wfRec to ⊏-rec)

-- shorthand for constructing _⊏_ proofs
pattern ↓₀ ∣P∣<∣Q∣ = inj₁ ∣P∣<∣Q∣
pattern ↓₁ ∣P∣≡∣Q∣ ∣ps∣<∣qs∣ = inj₂ (∣P∣≡∣Q∣ , inj₁ ∣ps∣<∣qs∣)
pattern ↓₂ ∣P∣≡∣Q∣ ∣ps∣≡∣qs∣ ∣αss∣<∣βss∣ = inj₂ (∣P∣≡∣Q∣ , inj₂ (∣ps∣≡∣qs∣ , ∣αss∣<∣βss∣))

--------------------------------------------------------------------------------

∥—*∥ : ∀ αs n → ∥ —* {αs} ∥ n ≡ n
∥—*∥ []       n = refl
∥—*∥ (α ∷ αs) n = ∥—*∥ αs n

sum-++ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ []       ys = refl
sum-++ (x ∷ xs) ys rewrite sum-++ xs ys = sym (+-assoc x (sum xs) (sum ys))

∥∥-++ : (psmat psmat' : PatternStackMatrix αss)
  → ∥ psmat ++ psmat' ∥ˢᵐ ≡ ∥ psmat ∥ˢᵐ + ∥ psmat' ∥ˢᵐ
∥∥-++ psmat psmat'
  rewrite map-++ ∥_∥ˢ psmat psmat' | sum-++ (map ∥_∥ˢ psmat) (map ∥_∥ˢ psmat')
  = refl

∥∥-tail : (psmat : PatternStackMatrix ([] ∷ αss))
  → ∥ map tailAll psmat ∥ˢᵐ ≡ ∥ psmat ∥ˢᵐ
∥∥-tail [] = refl
∥∥-tail (([] ∷ pss) ∷ psmat) = cong (_ +_) (∥∥-tail psmat)

specialize'-≤ : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → ∥ specialize' c pss ∥ˢᵐ ≤ ∥ pss ∥ˢ
specialize'-≤ {d0} c ((— ∷ ps) ∷ pss)
  rewrite ∥—*∥ (argsTy (dataDefs sig d0) c) ∥ ps ∷ pss ∥ˢ
  | +-identityʳ ∥ ps ∷ pss ∥ˢ
  = ≤-refl
specialize'-≤ c ((con c' rs ∷ ps) ∷ pss) = lem (c ≟ c')
  where
    lem : (eq : Dec (c ≡ c'))
      → ∥ specializeConCase c rs ps pss eq ∥ˢᵐ
      ≤ suc ∥ rs ∷ ps ∷ pss ∥ˢ
    lem (False ⟨ _    ⟩) = z≤n
    lem (True  ⟨ refl ⟩)
      rewrite +-identityʳ ∥ rs ∷ ps ∷ pss ∥ˢ
      = n≤1+n ∥ rs ∷ ps ∷ pss ∥ˢ
specialize'-≤ c ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    ∥ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≡⟨ ∥∥-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss)) ⟩
    ∥ specialize' c ((r₁ ∷ ps) ∷ pss) ∥ˢᵐ + ∥ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≤⟨ +-mono-≤ (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss)) ⟩
    ∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ
  <⟨ n<1+n _ ⟩
    suc (∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ)
  ∎
  where open ≤-Reasoning

-- specialize does not increase the pattern matrix size
specialize-≤
  : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → ∥ specialize c psmat ∥ˢᵐ ≤ ∥ psmat ∥ˢᵐ
specialize-≤ c [] = ≤-refl
specialize-≤ c (ps ∷ psmat) rewrite ∥∥-++ (specialize' c ps) (specialize c psmat)
  = +-mono-≤ (specialize'-≤ c ps) (specialize-≤ c psmat)

specialize'-< : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → c ∈ˢ pss
  → ∥ specialize' c pss ∥ˢᵐ < ∥ pss ∥ˢ
specialize'-< c ((con c' rs ∷ ps) ∷ pss) c≡c' = lem (c ≟ c')
  where
    lem : (eq : Dec (c ≡ c'))
      → ∥ specializeConCase c rs ps pss eq ∥ˢᵐ
      < suc ∥ rs ∷ ps ∷ pss ∥ˢ
    lem (False ⟨ c≢c' ⟩) = contradiction c≡c' c≢c'
    lem (True  ⟨ refl ⟩)
      rewrite +-identityʳ ∥ rs ∷ ps ∷ pss ∥ˢ
      = ≤-refl
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Left h) =
  begin
    suc ∥ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≡⟨ cong suc (∥∥-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (∥ specialize' c ((r₁ ∷ ps) ∷ pss) ∥ˢᵐ + ∥ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ)
  <⟨ s<s (+-mono-<-≤ (specialize'-< c ((r₁ ∷ ps) ∷ pss) h) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ)
  ∎
  where open ≤-Reasoning
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Right h) =
  begin
    suc ∥ specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≡⟨ cong suc (∥∥-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (∥ specialize' c ((r₁ ∷ ps) ∷ pss) ∥ˢᵐ + ∥ specialize' c ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ)
  <⟨ s<s (+-mono-≤-< (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-< c ((r₂ ∷ ps) ∷ pss) h)) ⟩
    suc (∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ)
  ∎
  where open ≤-Reasoning

-- specialize strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
specialize-< : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → c ∈ˢᵐ psmat
  → ∥ specialize c psmat ∥ˢᵐ < ∥ psmat ∥ˢᵐ
specialize-< c (pss ∷ psmat) (here h)
  rewrite ∥∥-++ (specialize' c pss) (specialize c psmat)
  = +-mono-<-≤ (specialize'-< c pss h) (specialize-≤ c psmat)
specialize-< c (pss ∷ psmat) (there h)
  rewrite ∥∥-++ (specialize' c pss) (specialize c psmat)
  = +-mono-≤-< (specialize'-≤ c pss) (specialize-< c psmat h)

default'-≤ : (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → ∥ default' pss ∥ˢᵐ ≤ ∥ pss ∥ˢ
default'-≤ ((— ∷ ps) ∷ pss)
  rewrite +-identityʳ ∥ ps ∷ pss ∥ˢ
  = ≤-refl
default'-≤ ((con _ _ ∷ ps) ∷ pss) = z≤n
default'-≤ ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    ∥ default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≡⟨ ∥∥-++ (default' ((r₁ ∷ ps) ∷ pss)) (default' ((r₂ ∷ ps) ∷ pss)) ⟩
    ∥ default' ((r₁ ∷ ps) ∷ pss) ∥ˢᵐ + ∥ default' ((r₂ ∷ ps) ∷ pss) ∥ˢᵐ
  ≤⟨ +-mono-≤ (default'-≤ ((r₁ ∷ ps) ∷ pss)) (default'-≤ ((r₂ ∷ ps) ∷ pss)) ⟩
    ∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ
  <⟨ n<1+n _ ⟩
    suc (∥ (r₁ ∷ ps) ∷ pss ∥ˢ + ∥ (r₂ ∷ ps) ∷ pss ∥ˢ)
  ∎
  where open ≤-Reasoning

-- default does not increase the pattern matrix size
default-≤ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → ∥ default_ psmat ∥ˢᵐ ≤ ∥ psmat ∥ˢᵐ
default-≤ [] = ≤-refl
default-≤ (ps ∷ psmat) rewrite ∥∥-++ (default' ps) (default_ psmat)
  = +-mono-≤ (default'-≤ ps) (default-≤ psmat)

--------------------------------------------------------------------------------
-- Each step strictly reduces the problem size

{-

   +---------------------------+---------------+-----------+------------+
   |    step    \   measure    |  ∥ psmat ∥ˢᵐ  |  ∥ ps ∥ˢ  |  ∥ αss ∥ᵗ  |
   +---------------------------+---------------+-----------+------------+
   | tail case                 |       =       |     =     |     <      |
   | con case                  |       ≤       |     <     |     ?      |
   | wildcard case (missing)   |       ≤       |     =     |     <      |
   | wildcard case (complete)  |       <       |     =     |     ?      |
   | or case                   |       =       |     <     |     =      |
   +---------------------------+---------------+-----------+------------+

-}

tail-⊏ : (psmat : PatternStackMatrix ([] ∷ αss)) (pss : PatternStack αss)
  → (_ , map tailAll psmat , pss) ⊏ (_ , psmat , [] ∷ pss)
tail-⊏ psmat pss = ↓₂ (∥∥-tail psmat) refl (n<1+n _)

-- specialize strictly reduces the problem size
specializeCon-⊏ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (c : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , specialize c psmat , rs ∷ ps ∷ pss) ⊏ (_ , psmat , (con c rs ∷ ps) ∷ pss)
specializeCon-⊏ psmat c rs ps pss with m≤n⇒m<n∨m≡n (specialize-≤ c psmat)
... | inj₁ ∣specPsmat∣<∣psmat∣ = ↓₀ ∣specPsmat∣<∣psmat∣
... | inj₂ ∣specPsmat∣≡∣psmat∣ = ↓₁ ∣specPsmat∣≡∣psmat∣ (n<1+n _)

-- default strictly reduces the problem size
default-⊏ : (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → (_ , default_ psmat , qs ∷ pss) ⊏ (_ , psmat , (— ∷ qs) ∷ pss)
default-⊏ psmat qs pss with m≤n⇒m<n∨m≡n (default-≤ psmat)
... | inj₁ ∣defPsmat∣<∣psmat∣ = ↓₀ ∣defPsmat∣<∣psmat∣
... | inj₂ ∣defPsmat∣≡∣psmat∣ = ↓₂ ∣defPsmat∣≡∣psmat∣ refl (n<1+n _)

-- specialize strictly reduces the problem size if the constructor is in the first column of the matrix
specializeWild-⊏
  : (c : NameCon d) (psmat : PatternStackMatrix ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → c ∈ˢᵐ psmat
  → (_ , specialize c psmat , —* ∷ qs ∷ pss) ⊏ (_ , psmat , (— ∷ qs) ∷ pss)
specializeWild-⊏ {d0} c psmat qs pss h
  rewrite ∥—*∥ (argsTy (dataDefs sig d0) c) ∥ qs ∷ pss ∥ˢ
  = ↓₀ (specialize-< c psmat h)

-- Choosing the left pattern strictly reduces the problem size
or-⊏ₗ : (psmat : PatternStackMatrix ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , psmat , (r₁ ∷ ps) ∷ pss) ⊏ (_ , psmat , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
or-⊏ₗ psmat r₁ r₂ ps pss =
  ↓₁ refl (m≤m+n _ ∥ (r₂ ∷ ps) ∷ pss ∥ˢ)

-- Choosing the right pattern strictly reduces the problem size
or-⊏ᵣ : (psmat : PatternStackMatrix ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , psmat , (r₂ ∷ ps) ∷ pss) ⊏ (_ , psmat , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
or-⊏ᵣ psmat r₁ r₂ ps pss =
  ↓₁ refl (s<s (m≤n+m _ ∥ (r₁ ∷ ps) ∷ pss ∥ˢ))

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
    → (∀ c → c ∈ˢᵐ psmat → UsefulAcc (specialize c psmat) (—* ∷ ps ∷ pss))
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
∀UsefulAcc : (psmat : PatternStackMatrix αss) (ps : PatternStack αss)
  → UsefulAcc psmat ps
∀UsefulAcc psmat ps =
  ⊏-rec _ (λ (_ , psmat , ps) → UsefulAcc psmat ps)
    (λ where
      (αss , psmat , []) rec → done
      (αss , psmat , [] ∷ pss) rec →
        tailStep (rec (tail-⊏ psmat pss))
      (αss , psmat , (con c rs ∷ ps) ∷ pss) rec →
        conStep (rec (specializeCon-⊏ psmat c rs ps pss))
      (αss , psmat , (r₁ ∣ r₂ ∷ ps) ∷ pss) rec →
        orStep
          (rec (or-⊏ₗ psmat r₁ r₂ ps pss))
          (rec (or-⊏ᵣ psmat r₁ r₂ ps pss))
      ((TyData d ∷ αs) ∷ αss , psmat , (— ∷ ps) ∷ pss) rec →
        wildStep
          (rec (default-⊏ psmat ps pss))
          (λ c h → rec (specializeWild-⊏ c psmat ps pss h)))
    (_ , psmat , ps)
