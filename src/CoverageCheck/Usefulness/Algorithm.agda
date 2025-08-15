open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

module CoverageCheck.Usefulness.Algorithm
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    α β : Type
    αs βs : Types
    d : NameData
    @0 α0 β0 : Type
    @0 αs0 βs0 : Types
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Raw algorithm

module _ ⦃ sig : Signature ⦄ {d : NameData} (c : NameCon d)
  (let αs = argsTy (dataDefs sig d) c)
  where

  -- Specialisation: filters out clauses whose first pattern does not match a value of the form `con c -`.

  specialiseAuxConCase : {c' : NameCon d}
    (let @0 αs' : Types
         αs' = argsTy (dataDefs sig d) c')
    (rs : Patterns αs') (ps : Patterns βs0)
    (eq : Dec (c ≡ c'))
    → PatternMatrix (αs ◂◂ βs0)
  specialiseAuxConCase rs ps eq =
    ifDec eq (λ where ⦃ refl ⦄ → (rs ◂◂ᵖ ps) ∷ []) []
  {-# COMPILE AGDA2HS specialiseAuxConCase inline #-}

  specialiseAux : Patterns (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialiseAux (—         ◂ ps) = (—* ◂◂ᵖ ps) ∷ []
  specialiseAux (con c' rs ◂ ps) = specialiseAuxConCase rs ps (c ≟ c')
  specialiseAux (r₁ ∣ r₂   ◂ ps) = specialiseAux (r₁ ◂ ps) ++ specialiseAux (r₂ ◂ ps)
  {-# COMPILE AGDA2HS specialiseAux #-}

  specialise : PatternMatrix (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialise = concatMap specialiseAux
  {-# COMPILE AGDA2HS specialise #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Default matrix: filters out clauses whose first pattern is a constructor pattern
  defaultAux : Patterns (α0 ◂ αs0) → PatternMatrix αs0
  defaultAux (—       ◂ ps) = ps ∷ []
  defaultAux (con _ _ ◂ ps) = []
  defaultAux (r₁ ∣ r₂ ◂ ps) = defaultAux (r₁ ◂ ps) ++ defaultAux (r₂ ◂ ps)
  {-# COMPILE AGDA2HS defaultAux #-}

  default' : PatternMatrix (α0 ◂ αs0) → PatternMatrix αs0
  default' = concatMap defaultAux
  {-# COMPILE AGDA2HS default' #-}


module Raw where

  module _ ⦃ @0 sig : Signature ⦄ where

    infix 4 elemRootCons

    elemRootCons : (c : NameCon d0) (p : Pattern (TyData d0)) → Bool
    syntax elemRootCons c p = c ∈ᵇ p
    c ∈ᵇ —         = False
    c ∈ᵇ con c' ps = value (c ≟ c')
    c ∈ᵇ (p ∣ q)   = c ∈ᵇ p || c ∈ᵇ q
    {-# COMPILE AGDA2HS elemRootCons #-}


  module _ ⦃ sig : Signature ⦄ where

    -- Is there a constructor that does not appear in the first column of P?
    existsMissingCon : (P : PatternMatrix (TyData d ◂ αs0)) → Bool
    existsMissingCon {d = d} pss =
      not (allNameCon (dataDefs sig d) λ c → any (λ ps → c ∈ᵇ headPattern ps) pss)
    {-# COMPILE AGDA2HS existsMissingCon #-}

    -- The core usefulness checking algorithm in the paper
    {-# TERMINATING #-}
    isUseful : (P : PatternMatrix αs) (ps : Patterns αs) → Bool
    isUseful {⌈⌉}            []      ⌈⌉              = True
    isUseful {⌈⌉}            (_ ∷ _) ⌈⌉              = False
    isUseful {TyData d ◂ αs} pss     (—        ◂ ps) =
      if existsMissingCon pss
        then isUseful (default' pss) ps
        else anyNameCon (dataDefs sig d) λ c → isUseful (specialise c pss) (—* ◂◂ᵖ ps)
    isUseful {TyData d ◂ αs} pss     (con c rs ◂ ps) = isUseful (specialise c pss) (rs ◂◂ᵖ ps)
    isUseful {TyData d ◂ αs} pss     (r₁ ∣ r₂  ◂ ps) = isUseful pss (r₁ ◂ ps) || isUseful pss (r₂ ◂ ps)
    {-# COMPILE AGDA2HS isUseful #-}

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄ where

  infix 4 _∈_ _∉_ decElemRootCons

  -- Does c appear in the set of root constructors of p?
  @0 _∈_ : NameCon d0 → Pattern (TyData d0) → Set
  c ∈ —         = ⊥
  c ∈ con c' ps = c ≡ c'
  c ∈ (p ∣ q)   = Either (c ∈ p) (c ∈ q)

  @0 _∉_ : NameCon d0 → Pattern (TyData d0) → Set
  c ∉ p = ¬ c ∈ p

  decElemRootCons : (c : NameCon d0) (p : Pattern (TyData d0)) → Dec (c ∈ p)
  syntax decElemRootCons c p = c ∈? p
  c ∈? —         = False ⟨ id ⟩
  c ∈? con c' ps = c ≟ c'
  c ∈? (p ∣ q)   = eitherDec (c ∈? p) (c ∈? q)
  {-# COMPILE AGDA2HS decElemRootCons #-}


module _ ⦃ sig : Signature ⦄ {d : NameData} where

  -- Is there a constructor that does not appear in the first column of P?
  decExistsMissingCon : (P : PatternMatrix (TyData d ◂ αs0))
    → Either
        (∃[ c ∈ NameCon d ] All (λ ps → c ∉ headPattern ps) P)
        (Erase (∀ c → Any (λ ps → c ∈ headPattern ps) P))
  decExistsMissingCon pss =
    case
      decAllNameCon (dataDefs sig d) (λ c →
        anyDec (λ ps → c ∈? headPattern ps) pss)
    of λ where
      (Left (Erased h)) → Right (Erased h)
      (Right (c ⟨ h ⟩)) → Left (c ⟨ (¬Any⇒All¬ pss h) ⟩)
  {-# COMPILE AGDA2HS decExistsMissingCon #-}


record Usefulness
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set)
  : Set where
  field
    nilNil : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → u [] ⌈⌉
    @0 consNil : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 ps : Patterns ⌈⌉} {@0 pss : PatternMatrix ⌈⌉}
      → ¬ u (ps ∷ pss) ⌈⌉

    orHead : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 pss : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0}
      → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps))
      → u pss (r₁ ∣ r₂ ◂ ps)
    @0 orHeadInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 pss : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0}
      → u pss (r₁ ∣ r₂ ◂ ps)
      → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps))

    conHead : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ βs0)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0}
      → u (specialise c pss) (rs ◂◂ᵖ ps)
      → u pss (con c rs ◂ ps)
    @0 conHeadInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ βs0)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0}
      → u pss (con c rs ◂ ps)
      → u (specialise c pss) (rs ◂◂ᵖ ps)

    wildHeadMiss : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → ∃[ c ∈ NameCon d ] All (λ ps → c ∉ headPattern ps) pss
      → u (default' pss) ps
      → u pss (— ◂ ps)
    @0 wildHeadMissInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → ∃[ c ∈ NameCon d ] All (λ ps → c ∉ headPattern ps) pss
      → u pss (— ◂ ps)
      → u (default' pss) ps

    wildHeadComp : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → @0 (∀ c → Any (λ ps → c ∈ headPattern ps) pss)
      → Σ[ c ∈ NameCon d ] u (specialise c pss) (—* ◂◂ᵖ ps)
      → u pss (— ◂ ps)
    @0 wildHeadCompInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → (∀ c → Any (λ ps → c ∈ headPattern ps) pss)
      → u pss (— ◂ ps)
      → Σ[ c ∈ NameCon d ] u (specialise c pss) (—* ◂◂ᵖ ps)

open Usefulness ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Usefulness class #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Specialized accessibility predicate for usefulness checking algorithm
  -- for separating termination proof from the algorithm
  -- This method is due to Ana Bove 2003.
  data @0 UsefulAcc : (P : PatternMatrix αs) (ps : Patterns αs) → Set where
    done : {P : PatternMatrix ⌈⌉} → UsefulAcc P ⌈⌉

    step-wild : {P : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
      → (∃[ c ∈ _ ] All (λ ps → c ∉ headPattern ps) P → UsefulAcc (default' P) ps)
      → (∀ c → Any (λ ps → c ∈ headPattern ps) P → UsefulAcc (specialise c P) (—* ◂◂ᵖ ps))
      → UsefulAcc P (— ◂ ps)

    step-con : {P : PatternMatrix (TyData d ◂ βs)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {rs : Patterns αs} {ps : Patterns βs}
      → UsefulAcc (specialise c P) (rs ◂◂ᵖ ps)
      → UsefulAcc P (con c rs ◂ ps)

    step-∣ : {P : PatternMatrix (α ◂ αs)} {p q : Pattern α} {ps : Patterns αs}
      → UsefulAcc P (p ◂ ps)
      → UsefulAcc P (q ◂ ps)
      → UsefulAcc P (p ∣ q ◂ ps)


module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful : (P : PatternMatrix αs) (ps : Patterns αs) → @0 UsefulAcc P ps → DecP (u P ps)
  decUseful {⌈⌉}            []      ⌈⌉              done             = Yes nilNil
  decUseful {⌈⌉}            (_ ∷ _) ⌈⌉              done             = No consNil
  decUseful {TyData d ◂ αs} pss     (— ◂ ps)        (step-wild h h') =
    case decExistsMissingCon pss of λ where
      (Left miss)  →
        mapDecP (wildHeadMiss miss) (wildHeadMissInv miss)
          (decUseful (default' pss) ps (h miss))
      (Right (Erased comp)) →
        mapDecP (wildHeadComp comp) (wildHeadCompInv comp)
          (decPAnyNameCon (dataDefs sig d) λ c →
            decUseful (specialise c pss) (—* ◂◂ᵖ ps) (h' c (comp c)))
  decUseful {TyData d ◂ αs} pss     (con c rs ◂ ps) (step-con h)     =
    mapDecP conHead conHeadInv (decUseful (specialise c pss) (rs ◂◂ᵖ ps) h)
  decUseful {TyData d ◂ αs} pss     (r₁ ∣ r₂  ◂ ps) (step-∣ h h')    =
    mapDecP orHead orHeadInv
      (eitherDecP (decUseful pss (r₁ ◂ ps) h) (decUseful pss (r₂ ◂ ps) h'))
  {-# COMPILE AGDA2HS decUseful #-}

--------------------------------------------------------------------------------
-- Termination

{-

       | ps size + P size | αs len |
-------+------------------+--------+
wild 1 |    = + ≤ ⇒ ≤     |   <    |
wild 2 |    = + < ⇒ <     |  <=>   |
con    |    < + ≤ ⇒ <     |  <=>   |
or     |    < + = ⇒ <     |   =    |

-}

module @0 _ ⦃ sig : Signature ⦄ where
  open import Data.List.Properties
    using (sum-++; map-++; ++-identityʳ)
  open import Data.Nat.Base
    using (ℕ; _+_; zero; suc; _≤_; _<_; s<s)
  open import Data.Nat.Induction
    using (<-wellFounded)
  open import Data.Nat.Properties
    using (+-identityʳ;
          ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
          n<1+n; 0<1+n; <⇒≤; +-monoˡ-<; +-monoʳ-<;
          +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)
  open import Data.Product
    using ()
    renaming (_×_ to _×ₚ_; _,_ to _,ₚ_)
  open import Data.Product.Relation.Binary.Lex.Strict
    using (×-Lex; ×-wellFounded)
  open import Data.Sum using (inj₁; inj₂)
  open import Function.Base using (_on_)
  open import Induction.WellFounded using (WellFounded; Acc; acc)
  open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)

  patsSize : Patterns αs0 → Nat → Nat
  patsSize ⌈⌉              n = n
  patsSize (—        ◂ ps) n = patsSize ps n
  patsSize (con c rs ◂ ps) n = suc (patsSize rs (patsSize ps n))
  patsSize (r₁ ∣ r₂  ◂ ps) n = suc (patsSize (r₁ ◂ ps) n + patsSize (r₂ ◂ ps) n)

  patMatSize : PatternMatrix αs0 → Nat
  patMatSize P = sum (map (flip patsSize 0) P)

  patsSize-◂◂ : (ps : Patterns αs) (qs : Patterns βs) (n : Nat)
    → patsSize (ps ◂◂ᵖ qs) n ≡ patsSize ps (patsSize qs n)
  patsSize-◂◂ ⌈⌉              qs n = refl
  patsSize-◂◂ (—        ◂ ps) qs n = patsSize-◂◂ ps qs n
  patsSize-◂◂ (con c rs ◂ ps) qs n = cong (suc ∘ patsSize rs) (patsSize-◂◂ ps qs n)
  patsSize-◂◂ (r₁ ∣ r₂  ◂ ps) qs n = cong suc (cong₂ _+_ (patsSize-◂◂ (r₁ ◂ ps) qs n) (patsSize-◂◂ (r₂ ◂ ps) qs n))

  patsSize—* : ∀ αs n → patsSize (—* {αs = αs}) n ≡ n
  patsSize—* ⌈⌉       n = refl
  patsSize—* (α ◂ αs) n = patsSize—* αs n

  patMatSize-◂◂ : (P Q : PatternMatrix αs0) → patMatSize (P ++ Q) ≡ patMatSize P + patMatSize Q
  patMatSize-◂◂ P Q
    rewrite map-++ (flip patsSize 0) P Q
    | sum-++ (map (flip patsSize 0) P) (map (flip patsSize 0) Q)
    = refl

  specialiseAux-≤ : (c : NameCon d0) (ps : Patterns (TyData d0 ◂ αs0))
    → patMatSize (specialiseAux c ps) ≤ patsSize ps 0
  specialiseAux-≤ {d0} c (— ◂ ps)
    rewrite patsSize-◂◂ (—* {αs = argsTy (dataDefs sig d0) c}) ps 0
    | patsSize—* (argsTy (dataDefs sig d0) c) (patsSize ps 0)
    | +-identityʳ (patsSize ps 0)
    = ≤-refl
  specialiseAux-≤ c (con c' rs ◂ ps) = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → patMatSize (specialiseAuxConCase c rs ps eq)
        ≤ suc (patsSize rs (patsSize ps 0))
      lem (False ⟨ _ ⟩)   = <⇒≤ 0<1+n
      lem (True ⟨ refl ⟩)
          rewrite patsSize-◂◂ rs ps 0
          | +-identityʳ (patsSize rs (patsSize ps 0))
          = n≤1+n (patsSize rs (patsSize ps 0))
  specialiseAux-≤ c (r₁ ∣ r₂ ◂ ps) =
    -- rewrite messed up termination check, so do it manually
    begin
      patMatSize (specialiseAux c (r₁ ◂ ps) ++ specialiseAux c (r₂ ◂ ps))
    ≡⟨ patMatSize-◂◂ (specialiseAux c (r₁ ◂ ps)) (specialiseAux c (r₂ ◂ ps)) ⟩
      patMatSize (specialiseAux c (r₁ ◂ ps)) + patMatSize (specialiseAux c (r₂ ◂ ps))
    ≤⟨ +-mono-≤ (specialiseAux-≤ c (r₁ ◂ ps)) (specialiseAux-≤ c (r₂ ◂ ps)) ⟩
      patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0
    <⟨ n<1+n _ ⟩
      suc (patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- specialise does not increase the pattern matrix size
  specialise-≤ : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0))
    → patMatSize (specialise c P) ≤ patMatSize P
  specialise-≤ c []       = ≤-refl
  specialise-≤ c (ps ∷ P) rewrite patMatSize-◂◂ (specialiseAux c ps) (specialise c P)
    = +-mono-≤ (specialiseAux-≤ c ps) (specialise-≤ c P)

  ∈⇒specialiseAux-< : (c : NameCon d0) (ps : Patterns (TyData d0 ◂ αs0))
    → c ∈ headPattern ps
    → patMatSize (specialiseAux c ps) < patsSize ps 0
  ∈⇒specialiseAux-< c (con c' rs ◂ ps) c≡c' = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → patMatSize (specialiseAuxConCase c rs ps eq)
        < suc (patsSize rs (patsSize ps 0))
      lem (False ⟨ c≢c' ⟩) = contradiction c≡c' c≢c'
      lem (True ⟨ refl ⟩)
          rewrite patsSize-◂◂ rs ps 0
          | +-identityʳ (patsSize rs (patsSize ps 0))
          = ≤-refl
  ∈⇒specialiseAux-< c (r₁ ∣ r₂ ◂ ps) (Left c∈r₁) =
    begin
      suc (patMatSize (specialiseAux c (r₁ ◂ ps) ++ specialiseAux c (r₂ ◂ ps)))
    ≡⟨ cong suc (patMatSize-◂◂ (specialiseAux c (r₁ ◂ ps)) (specialiseAux c (r₂ ◂ ps))) ⟩
      suc (patMatSize (specialiseAux c (r₁ ◂ ps)) + patMatSize (specialiseAux c (r₂ ◂ ps)))
    <⟨ s<s (+-mono-<-≤ (∈⇒specialiseAux-< c (r₁ ◂ ps) c∈r₁) (specialiseAux-≤ c (r₂ ◂ ps))) ⟩
      suc (patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning
  ∈⇒specialiseAux-< c (r₁ ∣ r₂ ◂ ps) (Right c∈r₂) =
    begin
      suc (patMatSize (specialiseAux c (r₁ ◂ ps) ++ specialiseAux c (r₂ ◂ ps)))
    ≡⟨ cong suc (patMatSize-◂◂ (specialiseAux c (r₁ ◂ ps)) (specialiseAux c (r₂ ◂ ps))) ⟩
      suc (patMatSize (specialiseAux c (r₁ ◂ ps)) + patMatSize (specialiseAux c (r₂ ◂ ps)))
    <⟨ s<s (+-mono-≤-< (specialiseAux-≤ c (r₁ ◂ ps)) (∈⇒specialiseAux-< c (r₂ ◂ ps) c∈r₂)) ⟩
      suc (patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- specialise strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
  ∈⇒specialise-< : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0))
    → Any (λ ps → c ∈ headPattern ps) P
    → patMatSize (specialise c P) < patMatSize P
  ∈⇒specialise-< c (ps ∷ P) (here c∈ps)
    rewrite patMatSize-◂◂ (specialiseAux c ps) (specialise c P)
    = +-mono-<-≤ (∈⇒specialiseAux-< c ps c∈ps) (specialise-≤ c P)
  ∈⇒specialise-< c (ps ∷ P) (there c∈P)
    rewrite patMatSize-◂◂ (specialiseAux c ps) (specialise c P)
    = +-mono-≤-< (specialiseAux-≤ c ps) (∈⇒specialise-< c P c∈P)

  defaultAux-≤ : (ps : Patterns (TyData d0 ◂ αs0)) → patMatSize (defaultAux ps) ≤ patsSize ps 0
  defaultAux-≤ (—       ◂ ps) rewrite +-identityʳ (patsSize ps 0) = ≤-refl
  defaultAux-≤ (con _ _ ◂ ps) = <⇒≤ 0<1+n
  defaultAux-≤ (r₁ ∣ r₂ ◂ ps) =
    begin
      patMatSize (defaultAux (r₁ ◂ ps) ++ defaultAux (r₂ ◂ ps))
    ≡⟨ patMatSize-◂◂ (defaultAux (r₁ ◂ ps)) (defaultAux (r₂ ◂ ps)) ⟩
      patMatSize (defaultAux (r₁ ◂ ps)) + patMatSize (defaultAux (r₂ ◂ ps))
    ≤⟨ +-mono-≤ (defaultAux-≤ (r₁ ◂ ps)) (defaultAux-≤ (r₂ ◂ ps)) ⟩
      patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0
    <⟨ n<1+n _ ⟩
      suc (patsSize (r₁ ◂ ps) 0 + patsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- default does not increase the pattern matrix size
  default-≤ : (P : PatternMatrix (TyData d0 ◂ αs0)) → patMatSize (default' P) ≤ patMatSize P
  default-≤ []       = ≤-refl
  default-≤ (ps ∷ P) rewrite patMatSize-◂◂ (defaultAux ps) (default' P)
    = +-mono-≤ (defaultAux-≤ ps) (default-≤ P)

  SomeProblem : Set
  SomeProblem = Σ[ αs ∈ _ ] PatternMatrix αs × Patterns αs

  problemSize : SomeProblem → ℕ ×ₚ ℕ
  problemSize (αs , (P , ps)) = (patMatSize P + patsSize ps 0) ,ₚ length αs

  -- Lexicographic ordering on SomeProblem
  _⊏_ : (P Q : SomeProblem) → Set
  _⊏_ = ×-Lex _≡_ _<_ _<_ on problemSize

  -- _⊏_ is well-founded
  ⊏-wellFounded : WellFounded _⊏_
  ⊏-wellFounded = on-wellFounded problemSize (×-wellFounded <-wellFounded <-wellFounded)

  -- specialise strictly reduces the problem size
  specialise-⊏ : (P : PatternMatrix (TyData d0 ◂ αs0)) (c : NameCon d0) (rs : Patterns (argsTy (dataDefs sig d0) c)) (ps : Patterns αs0)
    → (_ , (specialise c P , rs ◂◂ᵖ ps)) ⊏ (_ , (P , con c rs ◂ ps))
  specialise-⊏ P c rs ps
    rewrite patsSize-◂◂ rs ps 0
    = inj₁ (+-mono-≤-< (specialise-≤ c P) (n<1+n _))

  -- default strictly reduces the problem size
  default-⊏ : (P : PatternMatrix (TyData d0 ◂ αs0)) (qs : Patterns αs0)
    → (_ , (default' P , qs)) ⊏ (_ , (P , — ◂ qs))
  default-⊏ P qs with m≤n⇒m<n∨m≡n (default-≤ P)
  ... | inj₁ defaultP<P = inj₁ (+-monoˡ-< (patsSize qs 0) defaultP<P)
  ... | inj₂ defaultP≡P = inj₂ (cong (_+ patsSize qs 0) defaultP≡P ,ₚ n<1+n _)

  -- specialise strictly reduces the problem size if the constructor is in the first column of the matrix
  ∈⇒specialise-⊏ : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0)) (qs : Patterns αs0)
    → Any (λ ps → c ∈ headPattern ps) P
    → (_ , (specialise c P , —* ◂◂ᵖ qs)) ⊏ (_ , (P , — ◂ qs))
  ∈⇒specialise-⊏ {d0} c P qs c∈P
    rewrite patsSize-◂◂ (—* {αs = argsTy (dataDefs sig d0) c}) qs 0
    | patsSize—* (argsTy (dataDefs sig d0) c) (patsSize qs 0)
    = inj₁ (+-monoˡ-< (patsSize qs 0) (∈⇒specialise-< c P c∈P))

  -- Choosing the left pattern strictly reduces the problem size
  ∣-⊏ₗ : (P : PatternMatrix (α0 ◂ αs0)) (r₁ r₂ : Pattern α0) (ps : Patterns αs0)
    → (_ , (P , r₁ ◂ ps)) ⊏ (_ , (P , r₁ ∣ r₂ ◂ ps))
  ∣-⊏ₗ P r₁ r₂ ps =
    inj₁ (+-monoʳ-< (patMatSize P) (m≤m+n (suc (patsSize (r₁ ◂ ps) 0)) (patsSize (r₂ ◂ ps) 0)))

  -- Choosing the right pattern strictly reduces the problem size
  ∣-⊏ᵣ : (P : PatternMatrix (α0 ◂ αs0)) (r₁ r₂ : Pattern α0) (ps : Patterns αs0)
    → (_ , (P , r₂ ◂ ps)) ⊏ (_ , (P , r₁ ∣ r₂ ◂ ps))
  ∣-⊏ᵣ P r₁ r₂ ps =
    inj₁ (+-monoʳ-< (patMatSize P) (s<s (m≤n+m (patsSize (r₂ ◂ ps) 0) (patsSize (r₁ ◂ ps) 0))))

  ∀UsefulAccAux : (P : PatternMatrix αs0) (ps : Patterns αs0)
    → Acc _⊏_ (_ , (P , ps))
    → UsefulAcc P ps
  ∀UsefulAccAux P ⌈⌉ _ = done
  ∀UsefulAccAux {αs0 = TyData d ◂ αs0} P (— ◂ ps) (acc h) =
    step-wild
      (λ _ → ∀UsefulAccAux (default' P) ps (h (default-⊏ P ps)))
      (λ c c∈P → ∀UsefulAccAux (specialise c P) (—* ◂◂ᵖ ps) (h (∈⇒specialise-⊏ c P ps c∈P)))
  ∀UsefulAccAux P (con c rs ◂ ps) (acc h) =
    step-con (∀UsefulAccAux (specialise c P) (rs ◂◂ᵖ ps) (h (specialise-⊏ P c rs ps)))
  ∀UsefulAccAux P (r₁ ∣ r₂ ◂ ps) (acc h) =
    step-∣
      (∀UsefulAccAux P (r₁ ◂ ps) (h (∣-⊏ₗ P r₁ r₂ ps)))
      (∀UsefulAccAux P (r₂ ◂ ps) (h (∣-⊏ᵣ P r₁ r₂ ps)))

  ∀UsefulAcc : (P : PatternMatrix αs0) (ps : Patterns αs0) → UsefulAcc P ps
  ∀UsefulAcc P ps = ∀UsefulAccAux P ps (⊏-wellFounded _)

--------------------------------------------------------------------------------
-- Entrypoint

module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUsefulTerm : (pss : PatternMatrix αs) (ps : Patterns αs) → DecP (u pss ps)
  decUsefulTerm pss ps = decUseful (λ ⦃ sig' ⦄ → u ⦃ sig' ⦄) pss ps (∀UsefulAcc pss ps)
  {-# COMPILE AGDA2HS decUsefulTerm inline #-}
