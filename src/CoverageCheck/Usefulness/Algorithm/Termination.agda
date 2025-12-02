open import Data.Nat.Base using (_≤_; _<_; s<s)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using
  (+-identityʳ; +-assoc; ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
  n<1+n; 0<1+n; <⇒≤; +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)

open import CoverageCheck.Prelude hiding (Σ-syntax; _×_; _,_; _<_)
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

open import CoverageCheck.Usefulness.Algorithm.Types
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
-- Specialized accessibility predicate for usefulness checking algorithm
-- This method by Ana Bove allows separation of termination proof from the algorithm

data UsefulAcc : (P : PatternMatrixStack αss) (ps : PatternStack αss) → Type where
  done : {P : PatternMatrixStack []} → UsefulAcc P []

  tailStep : {P : PatternMatrixStack ([] ∷ αss)} {pss : PatternStack αss}
    → UsefulAcc (map tailAll P) pss
    → UsefulAcc P ([] ∷ pss)

  wildStep : {P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss)}
    → {ps : Patterns αs} {pss : PatternStack αss}
    → UsefulAcc (default_ P) (ps ∷ pss)
    → (∀ c → c ∈** P → UsefulAcc (specialize c P) (—* ∷ ps ∷ pss))
    → UsefulAcc P ((— ∷ ps) ∷ pss)

  conStep : {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)} {c : NameCon d}
    → (let αs = argsTy (dataDefs sig d) c)
    → {rs : Patterns αs} {ps : Patterns βs} {pss : PatternStack αss}
    → UsefulAcc (specialize c P) (rs ∷ ps ∷ pss)
    → UsefulAcc P ((con c rs ∷ ps) ∷ pss)

  orStep : {P : PatternMatrixStack ((α ∷ αs) ∷ αss)}
    → {p q : Pattern α} {ps : Patterns αs} {pss : PatternStack αss}
    → UsefulAcc P ((p ∷ ps) ∷ pss)
    → UsefulAcc P ((q ∷ ps) ∷ pss)
    → UsefulAcc P ((p ∣ q ∷ ps) ∷ pss)

--------------------------------------------------------------------------------
-- Termination measures

patternsSize : Patterns αs → Nat → Nat
patternsSize []              n = n
patternsSize (—        ∷ ps) n = patternsSize ps n
patternsSize (con c rs ∷ ps) n = suc (patternsSize rs (patternsSize ps n))
patternsSize (r₁ ∣ r₂  ∷ ps) n = suc (patternsSize (r₁ ∷ ps) n + patternsSize (r₂ ∷ ps) n)

patternStackSize : PatternStack αss → Nat → Nat
patternStackSize []         n = n
patternStackSize (ps ∷ pss) n = patternsSize ps (patternStackSize pss n)

patternMatrixStackSize : PatternMatrixStack αss → Nat
patternMatrixStackSize P = sum (map (flip patternStackSize 0) P)

tyStackLength : TyStack → Nat
tyStackLength [] = 0
tyStackLength (αs ∷ αss) = suc (lengthNat αs + tyStackLength αss)

Input : Type
Input = Σ[ αss ∈ _ ] PatternMatrixStack αss × PatternStack αss

inputSize : Input → Nat × Nat × Nat
inputSize (αss , P , ps) =
  patternMatrixStackSize P , patternStackSize ps 0 , tyStackLength αss

-- Lexicographic ordering on Inputs
_⊏_ : Input → Input → Type
_⊏_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_) on inputSize

-- _⊏_ is well-founded
⊏-wellFounded : WellFounded _⊏_
⊏-wellFounded =
  on-wellFounded inputSize
    (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded))

-- shorthand for creating _⊏_ proofs
pattern ↓₀ ∣P∣<∣Q∣ = inj₁ ∣P∣<∣Q∣
pattern ↓₁ ∣P∣≡∣Q∣ ∣ps∣<∣qs∣ = inj₂ (∣P∣≡∣Q∣ , inj₁ ∣ps∣<∣qs∣)
pattern ↓₂ ∣P∣≡∣Q∣ ∣ps∣≡∣qs∣ ∣αss∣<∣βss∣ = inj₂ (∣P∣≡∣Q∣ , inj₂ (∣ps∣≡∣qs∣ , ∣αss∣<∣βss∣))

--------------------------------------------------------------------------------

patternsSize—* : ∀ αs n → patternsSize {αs} —* n ≡ n
patternsSize—* []       n = refl
patternsSize—* (α ∷ αs) n = patternsSize—* αs n

sum-++ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ []       ys = refl
sum-++ (x ∷ xs) ys rewrite sum-++ xs ys = sym (+-assoc x (sum xs) (sum ys))

patternMatrixStackSize-++ : (P Q : PatternMatrixStack αss)
  → patternMatrixStackSize (P ++ Q)
      ≡ patternMatrixStackSize P + patternMatrixStackSize Q
patternMatrixStackSize-++ P Q
  rewrite map-++ (flip patternStackSize 0) P Q
  | sum-++ (map (flip patternStackSize 0) P) (map (flip patternStackSize 0) Q)
  = refl

tail-≡ : (P : PatternMatrixStack ([] ∷ αss))
  → patternMatrixStackSize (map tailAll P) ≡ patternMatrixStackSize P
tail-≡ []               = refl
tail-≡ (([] ∷ pss) ∷ P) = cong (_ +_) (tail-≡ P)

specialize'-≤ : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → patternMatrixStackSize (specialize' c pss) ≤ patternStackSize pss 0
specialize'-≤ {d0} c ((— ∷ ps) ∷ pss)
  rewrite patternsSize—* (argsTy (dataDefs sig d0) c) (patternStackSize (ps ∷ pss) 0)
  | +-identityʳ (patternStackSize (ps ∷ pss) 0)
  = ≤-refl
specialize'-≤ c ((con c' rs ∷ ps) ∷ pss) = lem (c ≟ c')
  where
    lem : (eq : Dec (c ≡ c'))
      → patternMatrixStackSize (specializeConCase c rs ps pss eq)
      ≤ suc (patternStackSize (rs ∷ ps ∷ pss) 0)
    lem (False ⟨ _    ⟩) = <⇒≤ 0<1+n
    lem (True  ⟨ refl ⟩)
      rewrite +-identityʳ (patternStackSize (rs ∷ ps ∷ pss) 0)
      = n≤1+n (patternStackSize (rs ∷ ps ∷ pss) 0)
specialize'-≤ c ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss))
  ≡⟨ patternMatrixStackSize-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss)) ⟩
    patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss)) + patternMatrixStackSize (specialize' c ((r₂ ∷ ps) ∷ pss))
  ≤⟨ +-mono-≤ (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss)) ⟩
    patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0
  <⟨ n<1+n _ ⟩
    suc (patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0)
  ∎
  where open ≤-Reasoning

-- specialize does not increase the pattern matrix size
specialize-≤ : (c : NameCon d) (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → patternMatrixStackSize (specialize c P) ≤ patternMatrixStackSize P
specialize-≤ c []       = ≤-refl
specialize-≤ c (ps ∷ P) rewrite patternMatrixStackSize-++ (specialize' c ps) (specialize c P)
  = +-mono-≤ (specialize'-≤ c ps) (specialize-≤ c P)

specialize'-< : (c : NameCon d) (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → c ∈* pss
  → patternMatrixStackSize (specialize' c pss) < patternStackSize pss 0
specialize'-< c ((con c' rs ∷ ps) ∷ pss) c≡c' = lem (c ≟ c')
  where
    lem : (eq : Dec (c ≡ c'))
      → patternMatrixStackSize (specializeConCase c rs ps pss eq)
      < suc (patternStackSize (rs ∷ ps ∷ pss) 0)
    lem (False ⟨ c≢c' ⟩) = contradiction c≡c' c≢c'
    lem (True  ⟨ refl ⟩)
      rewrite +-identityʳ (patternStackSize (rs ∷ ps ∷ pss) 0)
      = ≤-refl
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Left h) =
  begin
    suc (patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss)))
  ≡⟨ cong suc (patternMatrixStackSize-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss)) + patternMatrixStackSize (specialize' c ((r₂ ∷ ps) ∷ pss)))
  <⟨ s<s (+-mono-<-≤ (specialize'-< c ((r₁ ∷ ps) ∷ pss) h) (specialize'-≤ c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0)
  ∎
  where open ≤-Reasoning
specialize'-< c ((r₁ ∣ r₂ ∷ ps) ∷ pss) (Right h) =
  begin
    suc (patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss) ++ specialize' c ((r₂ ∷ ps) ∷ pss)))
  ≡⟨ cong suc (patternMatrixStackSize-++ (specialize' c ((r₁ ∷ ps) ∷ pss)) (specialize' c ((r₂ ∷ ps) ∷ pss))) ⟩
    suc (patternMatrixStackSize (specialize' c ((r₁ ∷ ps) ∷ pss)) + patternMatrixStackSize (specialize' c ((r₂ ∷ ps) ∷ pss)))
  <⟨ s<s (+-mono-≤-< (specialize'-≤ c ((r₁ ∷ ps) ∷ pss)) (specialize'-< c ((r₂ ∷ ps) ∷ pss) h)) ⟩
    suc (patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0)
  ∎
  where open ≤-Reasoning

-- specialize strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
specialize-< : (c : NameCon d) (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → c ∈** P
  → patternMatrixStackSize (specialize c P) < patternMatrixStackSize P
specialize-< c (pss ∷ P) (here h)
  rewrite patternMatrixStackSize-++ (specialize' c pss) (specialize c P)
  = +-mono-<-≤ (specialize'-< c pss h) (specialize-≤ c P)
specialize-< c (pss ∷ P) (there h)
  rewrite patternMatrixStackSize-++ (specialize' c pss) (specialize c P)
  = +-mono-≤-< (specialize'-≤ c pss) (specialize-< c P h)

default'-≤ : (pss : PatternStack ((TyData d ∷ αs) ∷ αss))
  → patternMatrixStackSize (default' pss) ≤ patternStackSize pss 0
default'-≤ ((— ∷ ps) ∷ pss)
  rewrite +-identityʳ (patternStackSize (ps ∷ pss) 0)
  = ≤-refl
default'-≤ ((con _ _ ∷ ps) ∷ pss) = <⇒≤ 0<1+n
default'-≤ ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
  begin
    patternMatrixStackSize (default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss))
  ≡⟨ patternMatrixStackSize-++ (default' ((r₁ ∷ ps) ∷ pss)) (default' ((r₂ ∷ ps) ∷ pss)) ⟩
    patternMatrixStackSize (default' ((r₁ ∷ ps) ∷ pss)) + patternMatrixStackSize (default' ((r₂ ∷ ps) ∷ pss))
  ≤⟨ +-mono-≤ (default'-≤ ((r₁ ∷ ps) ∷ pss)) (default'-≤ ((r₂ ∷ ps) ∷ pss)) ⟩
    patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0
  <⟨ n<1+n _ ⟩
    suc (patternStackSize ((r₁ ∷ ps) ∷ pss) 0 + patternStackSize ((r₂ ∷ ps) ∷ pss) 0)
  ∎
  where open ≤-Reasoning

-- default does not increase the pattern matrix size
default-≤ : (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → patternMatrixStackSize (default_ P) ≤ patternMatrixStackSize P
default-≤ [] = ≤-refl
default-≤ (ps ∷ P) rewrite patternMatrixStackSize-++ (default' ps) (default_ P)
  = +-mono-≤ (default'-≤ ps) (default-≤ P)

tail-⊏ : (P : PatternMatrixStack ([] ∷ αss)) (pss : PatternStack αss)
  → (_ , map tailAll P , pss) ⊏ (_ , P , [] ∷ pss)
tail-⊏ P pss = ↓₂ (tail-≡ P) refl (n<1+n _)

-- specialize strictly reduces the problem size
specializeCon-⊏ : (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → (c : NameCon d) (rs : Patterns (argsTy (dataDefs sig d) c))
  → (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , specialize c P , rs ∷ ps ∷ pss) ⊏ (_ , P , (con c rs ∷ ps) ∷ pss)
specializeCon-⊏ P c rs ps pss with m≤n⇒m<n∨m≡n (specialize-≤ c P)
... | inj₁ ∣specP∣<∣P∣ = ↓₀ ∣specP∣<∣P∣
... | inj₂ ∣specP∣≡∣P∣ = ↓₁ ∣specP∣≡∣P∣ (n<1+n _)

-- default strictly reduces the problem size
default-⊏ : (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → (_ , default_ P , qs ∷ pss) ⊏ (_ , P , (— ∷ qs) ∷ pss)
default-⊏ P qs pss with m≤n⇒m<n∨m≡n (default-≤ P)
... | inj₁ ∣defP∣<∣P∣ = ↓₀ ∣defP∣<∣P∣
... | inj₂ |defP∣≡∣P∣ = ↓₂ |defP∣≡∣P∣ refl (n<1+n _)

-- specialize strictly reduces the problem size if the constructor is in the first column of the matrix
specializeWild-⊏ : (c : NameCon d) (P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss))
  → (qs : Patterns αs) (pss : PatternStack αss)
  → c ∈** P
  → (_ , specialize c P , —* ∷ qs ∷ pss) ⊏ (_ , P , (— ∷ qs) ∷ pss)
specializeWild-⊏ {d0} c P qs pss h
  rewrite patternsSize—* (argsTy (dataDefs sig d0) c) (patternStackSize (qs ∷ pss) 0)
  = ↓₀ (specialize-< c P h)

-- Choosing the left pattern strictly reduces the problem size
chooseOr-⊏ₗ : (P : PatternMatrixStack ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , P , (r₁ ∷ ps) ∷ pss) ⊏ (_ , P , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
chooseOr-⊏ₗ P r₁ r₂ ps pss =
  ↓₁ refl (m≤m+n _ (patternStackSize ((r₂ ∷ ps) ∷ pss) 0))

-- Choosing the right pattern strictly reduces the problem size
chooseOr-⊏ᵣ : (P : PatternMatrixStack ((α ∷ αs) ∷ αss))
  → (r₁ r₂ : Pattern α) (ps : Patterns αs) (pss : PatternStack αss)
  → (_ , P , (r₂ ∷ ps) ∷ pss) ⊏ (_ , P , ((r₁ ∣ r₂) ∷ ps) ∷ pss)
chooseOr-⊏ᵣ P r₁ r₂ ps pss =
  ↓₁ refl (s<s (m≤n+m _ (patternStackSize ((r₁ ∷ ps) ∷ pss) 0)))

∀UsefulAcc' : (P : PatternMatrixStack αss) (pss : PatternStack αss)
  → Acc _⊏_ (_ , P , pss)
  → UsefulAcc P pss
∀UsefulAcc' P [] (acc _) = done
∀UsefulAcc' P ([] ∷ pss) (acc rec) =
  tailStep (∀UsefulAcc' (map tailAll P) pss (rec (tail-⊏ P pss)))
∀UsefulAcc' {αss = (TyData d ∷ αs) ∷ αss} P ((— ∷ ps) ∷ pss) (acc rec) =
  wildStep
    (∀UsefulAcc' (default_ P) (ps ∷ pss) (rec (default-⊏ P ps pss)))
    (λ c m → ∀UsefulAcc' (specialize c P) (—* ∷ ps ∷ pss) (rec (specializeWild-⊏ c P ps pss m)))
∀UsefulAcc' P ((con c rs ∷ ps) ∷ pss) (acc rec) =
  conStep (∀UsefulAcc' (specialize c P) (rs ∷ ps ∷ pss) (rec (specializeCon-⊏ P c rs ps pss)))
∀UsefulAcc' P ((r₁ ∣ r₂ ∷ ps) ∷ pss) (acc rec) =
  orStep
    (∀UsefulAcc' P ((r₁ ∷ ps) ∷ pss) (rec (chooseOr-⊏ₗ P r₁ r₂ ps pss)))
    (∀UsefulAcc' P ((r₂ ∷ ps) ∷ pss) (rec (chooseOr-⊏ᵣ P r₁ r₂ ps pss)))

∀UsefulAcc : (P : PatternMatrixStack αss) (ps : PatternStack αss) → UsefulAcc P ps
∀UsefulAcc P ps = ∀UsefulAcc' P ps (⊏-wellFounded _)
