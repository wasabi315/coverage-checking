open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)

module CoverageCheck.Usefulness.Algorithm
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Raw algorithm

module _ ⦃ sig : Signature ⦄ {d : NameData} (c : NameCon d)
  (let αs = argsTy (dataDefs sig d) c)
  where

  -- Specialisation: filters out clauses whose first pattern does not match a value of the form `con c -`.

  specialize'ConCase : {c' : NameCon d}
    (let @0 αs' : Tys
         αs' = argsTy (dataDefs sig d) c')
    (rs : Patterns αs') (ps : Patterns βs0)
    (eq : Dec (c ≡ c'))
    → PatternMatrix (αs ◂◂ βs0)
  specialize'ConCase rs ps eq =
    ifDec eq (λ where ⦃ refl ⦄ → (rs ◂◂ᵖ ps) ∷ []) []
  {-# COMPILE AGDA2HS specialize'ConCase inline #-}

  specialize' : Patterns (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialize' (—         ◂ ps) = (—* ◂◂ᵖ ps) ∷ []
  specialize' (con c' rs ◂ ps) = specialize'ConCase rs ps (c ≟ c')
  specialize' (r₁ ∣ r₂   ◂ ps) = specialize' (r₁ ◂ ps) ++ specialize' (r₂ ◂ ps)
  {-# COMPILE AGDA2HS specialize' #-}

  specialize : PatternMatrix (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialize = concatMap specialize'
  {-# COMPILE AGDA2HS specialize #-}


module _ ⦃ @0 sig : Signature ⦄ where

  rootConSet' : (p : Pattern (TyData d0)) → Set (NameCon d0)
  rootConSet' —         = Set.empty
  rootConSet' (con c _) = Set.singleton c
  rootConSet' (p ∣ q)   = Set.union (rootConSet' p) (rootConSet' q)
  {-# COMPILE AGDA2HS rootConSet' #-}

  rootConSet : (P : PatternMatrix (TyData d0 ◂ αs0)) → Set (NameCon d0)
  rootConSet pss = foldr (λ ps → Set.union (rootConSet' (headPattern ps))) Set.empty pss
  {-# COMPILE AGDA2HS rootConSet #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Default matrix: filters out clauses whose first pattern is a constructor pattern
  default' : Patterns (α0 ◂ αs0) → PatternMatrix αs0
  default' (—       ◂ ps) = ps ∷ []
  default' (con _ _ ◂ ps) = []
  default' (r₁ ∣ r₂ ◂ ps) = default' (r₁ ◂ ps) ++ default' (r₂ ◂ ps)
  {-# COMPILE AGDA2HS default' #-}

  default_ : PatternMatrix (α0 ◂ αs0) → PatternMatrix αs0
  default_ = concatMap default'
  {-# COMPILE AGDA2HS default_ #-}


module Raw where

  module _ ⦃ sig : Signature ⦄ where

    -- Is there a constructor that does not appear in the first column of P?
    existMissCon : (P : PatternMatrix (TyData d ◂ αs0)) → Bool
    existMissCon {d = d} pss = not (Set.null missConSet)
      where
        conSet missConSet : Set (NameCon d)
        conSet     = rootConSet pss
        missConSet = Set.difference (universalNameConSet (dataDefs sig d)) conSet
    {-# COMPILE AGDA2HS existMissCon #-}

    -- The core usefulness checking algorithm in the paper
    {-# TERMINATING #-}
    isUseful : (P : PatternMatrix αs) (ps : Patterns αs) → Bool
    isUseful {⌈⌉}            []      ⌈⌉              = True
    isUseful {⌈⌉}            (_ ∷ _) ⌈⌉              = False
    isUseful {TyData d ◂ αs} pss     (—        ◂ ps) =
      if existMissCon pss
        then isUseful (default_ pss) ps
        else anyNameCon (dataDefs sig d) λ c → isUseful (specialize c pss) (—* ◂◂ᵖ ps)
    isUseful {TyData d ◂ αs} pss     (con c rs ◂ ps) = isUseful (specialize c pss) (rs ◂◂ᵖ ps)
    isUseful {TyData d ◂ αs} pss     (r₁ ∣ r₂  ◂ ps) = isUseful pss (r₁ ◂ ps) || isUseful pss (r₂ ◂ ps)
    {-# COMPILE AGDA2HS isUseful #-}

--------------------------------------------------------------------------------

module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} where

  infix 4 _∈_ _∉_ _∈*_ _∉*_ _∈**_ _∉**_

  -- Does c appear in the set of root constructors of p?
  _∈_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∈ —         = ⊥
  c ∈ con c' ps = c ≡ c'
  c ∈ (p ∣ q)   = Either (c ∈ p) (c ∈ q)

  _∉_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∉ p = ¬ c ∈ p

  _∈*_ _∉*_ : NameCon d0 → Patterns (TyData d0 ◂ αs0) → Type
  c ∈* ps = c ∈ headPattern ps
  c ∉* ps = c ∉ headPattern ps

  _∈**_ _∉**_ : NameCon d0 → PatternMatrix (TyData d0 ◂ αs0) → Type
  c ∈** pss = Any (c ∈*_) pss
  c ∉** pss = All (c ∉*_) pss


module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} (@0 c : NameCon d0) where

  memberRootConSet' : (p : Pattern (TyData d0))
    → Reflects (c ∈ p) (Set.member c (rootConSet' p))
  memberRootConSet' — rewrite prop-member-empty c = id
  memberRootConSet' (con c' _) rewrite prop-member-singleton c c' = isEquality c c'
  memberRootConSet' (p ∣ q)
    rewrite prop-member-union c (rootConSet' p) (rootConSet' q)
    = eitherReflects (memberRootConSet' p) (memberRootConSet' q)

  memberRootConSet : (pss : PatternMatrix (TyData d0 ◂ αs0))
    → Reflects (c ∈** pss) (Set.member c (rootConSet pss))
  memberRootConSet ⌈⌉ rewrite prop-member-empty c = λ ()
  memberRootConSet (ps ◂ pss)
    rewrite prop-member-union c (rootConSet' (headPattern ps)) (rootConSet pss)
    = mapReflects
        (either here there)
        (λ where (here h) → Left h; (there h) → Right h)
        (eitherReflects (memberRootConSet' (headPattern ps)) (memberRootConSet pss))


module @0 _ ⦃ @0 sig : Signature ⦄
  {@0 d0} (@0 c : NameCon d0) (@0 pss : PatternMatrix (TyData d0 ◂ αs0))
  (let conSet     = rootConSet pss
       missConSet = Set.difference (universalNameConSet (dataDefs sig d0)) conSet)
  where

  notMemberMissConSet : Reflects (c ∈** pss) (not (Set.member c missConSet))
  notMemberMissConSet
    rewrite prop-member-difference c (universalNameConSet (dataDefs sig d0)) conSet
    | universalNameConSetUniversal (dataDefs sig d0) c
    | not-not (Set.member c conSet)
    = memberRootConSet c pss

  memberMissConSet : Reflects (c ∉** pss) (Set.member c missConSet)
  memberMissConSet rewrite sym (not-not (Set.member c missConSet)) =
    mapReflects (¬Any⇒All¬ _) All¬⇒¬Any (negReflects notMemberMissConSet)


module _ ⦃ sig : Signature ⦄ {d : NameData} where

  -- Are there constructors that does not appear in the first column of P?
  decExistMissCon : (P : PatternMatrix (TyData d ◂ αs0))
    → Either (∃[ c ∈ NameCon d ] c ∉** P) (Erase (∀ c → c ∈** P))
  decExistMissCon pss =
    case findMin missConSet of λ where
      (Left (Erased empty)) →
        Right (Erased λ c → extractTrue ⦃ cong not (empty c) ⦄ (notMemberMissConSet c pss))
      (Right (c ⟨ miss ⟩)) →
        Left (c ⟨ extractTrue ⦃ miss ⦄ (memberMissConSet c pss) ⟩)
    where
      conSet missConSet : Set (NameCon d)
      conSet     = rootConSet pss
      missConSet = Set.difference (universalNameConSet (dataDefs sig d)) conSet
  {-# COMPILE AGDA2HS decExistMissCon #-}


record Usefulness
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Type)
  : Type where
  field
    nilOkCase : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → u [] ⌈⌉

    @0 nilBadCase : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 ps : Patterns ⌈⌉} {@0 pss : PatternMatrix ⌈⌉}
      → ¬ u (ps ∷ pss) ⌈⌉

    orCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 pss : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0}
      → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps))
      → u pss (r₁ ∣ r₂ ◂ ps)

    @0 orCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 pss : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0}
      → u pss (r₁ ∣ r₂ ◂ ps)
      → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps))

    conCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ βs0)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0}
      → u (specialize c pss) (rs ◂◂ᵖ ps)
      → u pss (con c rs ◂ ps)

    @0 conCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ βs0)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0}
      → u pss (con c rs ◂ ps)
      → u (specialize c pss) (rs ◂◂ᵖ ps)

    wildMissCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → ∃[ c ∈ NameCon d ] c ∉** pss
      → u (default_ pss) ps
      → u pss (— ◂ ps)

    @0 wildMissCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → ∃[ c ∈ NameCon d ] c ∉** pss
      → u pss (— ◂ ps)
      → u (default_ pss) ps

    wildCompCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → @0 (∀ c → c ∈** pss)
      → Σ[ c ∈ NameCon d ] u (specialize c pss) (—* ◂◂ᵖ ps)
      → u pss (— ◂ ps)

    @0 wildCompCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 pss : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
      → @0 (∀ c → c ∈** pss)
      → u pss (— ◂ ps)
      → Σ[ c ∈ NameCon d ] u (specialize c pss) (—* ◂◂ᵖ ps)

open Usefulness ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Usefulness class #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Specialized accessibility predicate for usefulness checking algorithm
  -- for separating termination proof from the algorithm
  -- This method is due to Ana Bove 2003.
  data @0 UsefulAcc : (P : PatternMatrix αs) (ps : Patterns αs) → Type where
    done : {P : PatternMatrix ⌈⌉} → UsefulAcc P ⌈⌉

    step-wild : {P : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
      → (∃[ c ∈ _ ] c ∉** P → UsefulAcc (default_ P) ps)
      → (∀ c → c ∈** P → UsefulAcc (specialize c P) (—* ◂◂ᵖ ps))
      → UsefulAcc P (— ◂ ps)

    step-con : {P : PatternMatrix (TyData d ◂ βs)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {rs : Patterns αs} {ps : Patterns βs}
      → UsefulAcc (specialize c P) (rs ◂◂ᵖ ps)
      → UsefulAcc P (con c rs ◂ ps)

    step-∣ : {P : PatternMatrix (α ◂ αs)} {p q : Pattern α} {ps : Patterns αs}
      → UsefulAcc P (p ◂ ps)
      → UsefulAcc P (q ◂ ps)
      → UsefulAcc P (p ∣ q ◂ ps)


module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Type)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful : (P : PatternMatrix αs) (ps : Patterns αs) → @0 UsefulAcc P ps → DecP (u P ps)
  decUseful {⌈⌉}            []      ⌈⌉              done             = Yes nilOkCase
  decUseful {⌈⌉}            (_ ∷ _) ⌈⌉              done             = No nilBadCase
  decUseful {TyData d ◂ αs} pss     (— ◂ ps)        (step-wild h h') =
    case decExistMissCon pss of λ where
      (Left miss)  →
        mapDecP (wildMissCase miss) (wildMissCaseInv miss)
          (decUseful (default_ pss) ps (h miss))
      (Right (Erased comp)) →
        mapDecP (wildCompCase comp) (wildCompCaseInv comp)
          (decPAnyNameCon (dataDefs sig d) λ c →
            decUseful (specialize c pss) (—* ◂◂ᵖ ps) (h' c (comp c)))
  decUseful {TyData d ◂ αs} pss     (con c rs ◂ ps) (step-con h)     =
    mapDecP conCase conCaseInv (decUseful (specialize c pss) (rs ◂◂ᵖ ps) h)
  decUseful {TyData d ◂ αs} pss     (r₁ ∣ r₂  ◂ ps) (step-∣ h h')    =
    mapDecP orCase orCaseInv
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

module @0 _ ⦃ @0 sig : Signature ⦄ where
  open import Data.Nat.Base using (_≤_; _<_; s<s)
  open import Data.Nat.Induction using (<-wellFounded)
  open import Data.Nat.Properties
    using (+-identityʳ; +-assoc;
          ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
          n<1+n; 0<1+n; <⇒≤; +-monoˡ-<; +-monoʳ-<;
          +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)
  open import Data.Product using () renaming (_×_ to _×ₚ_; _,_ to infix -1 _,_)
  open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
  open import Data.Sum using (inj₁; inj₂)
  open import Function.Base using (_on_)
  open import Induction.WellFounded using (WellFounded; Acc; acc)
  open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)

  patternsSize : Patterns αs0 → Nat → Nat
  patternsSize ⌈⌉              n = n
  patternsSize (—        ◂ ps) n = patternsSize ps n
  patternsSize (con c rs ◂ ps) n = suc (patternsSize rs (patternsSize ps n))
  patternsSize (r₁ ∣ r₂  ◂ ps) n = suc (patternsSize (r₁ ◂ ps) n + patternsSize (r₂ ◂ ps) n)

  patternMatrixSize : PatternMatrix αs0 → Nat
  patternMatrixSize P = sum (map (flip patternsSize 0) P)

  patternsSize-◂◂ : (ps : Patterns αs) (qs : Patterns βs) (n : Nat)
    → patternsSize (ps ◂◂ᵖ qs) n ≡ patternsSize ps (patternsSize qs n)
  patternsSize-◂◂ ⌈⌉              qs n = refl
  patternsSize-◂◂ (—        ◂ ps) qs n = patternsSize-◂◂ ps qs n
  patternsSize-◂◂ (con c rs ◂ ps) qs n = cong (suc ∘ patternsSize rs) (patternsSize-◂◂ ps qs n)
  patternsSize-◂◂ (r₁ ∣ r₂  ◂ ps) qs n = cong suc (cong₂ _+_ (patternsSize-◂◂ (r₁ ◂ ps) qs n) (patternsSize-◂◂ (r₂ ◂ ps) qs n))

  patternsSize—* : ∀ αs n → patternsSize (—* {αs = αs}) n ≡ n
  patternsSize—* ⌈⌉       n = refl
  patternsSize—* (α ◂ αs) n = patternsSize—* αs n

  sum-++ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum xs + sum ys
  sum-++ []       ys = refl
  sum-++ (x ∷ xs) ys rewrite sum-++ xs ys = sym (+-assoc x (sum xs) (sum ys))

  patternMatrixSize-◂◂ : (P Q : PatternMatrix αs0) → patternMatrixSize (P ++ Q) ≡ patternMatrixSize P + patternMatrixSize Q
  patternMatrixSize-◂◂ P Q
    rewrite map-++ (flip patternsSize 0) P Q
    | sum-++ (map (flip patternsSize 0) P) (map (flip patternsSize 0) Q)
    = refl

  specialize'-≤ : (c : NameCon d0) (ps : Patterns (TyData d0 ◂ αs0))
    → patternMatrixSize (specialize' c ps) ≤ patternsSize ps 0
  specialize'-≤ {d0} c (— ◂ ps)
    rewrite patternsSize-◂◂ (—* {αs = argsTy (dataDefs sig d0) c}) ps 0
    | patternsSize—* (argsTy (dataDefs sig d0) c) (patternsSize ps 0)
    | +-identityʳ (patternsSize ps 0)
    = ≤-refl
  specialize'-≤ c (con c' rs ◂ ps) = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → patternMatrixSize (specialize'ConCase c rs ps eq)
        ≤ suc (patternsSize rs (patternsSize ps 0))
      lem (False ⟨ _ ⟩)   = <⇒≤ 0<1+n
      lem (True ⟨ refl ⟩)
          rewrite patternsSize-◂◂ rs ps 0
          | +-identityʳ (patternsSize rs (patternsSize ps 0))
          = n≤1+n (patternsSize rs (patternsSize ps 0))
  specialize'-≤ c (r₁ ∣ r₂ ◂ ps) =
    -- rewrite messed up termination check, so do it manually
    begin
      patternMatrixSize (specialize' c (r₁ ◂ ps) ++ specialize' c (r₂ ◂ ps))
    ≡⟨ patternMatrixSize-◂◂ (specialize' c (r₁ ◂ ps)) (specialize' c (r₂ ◂ ps)) ⟩
      patternMatrixSize (specialize' c (r₁ ◂ ps)) + patternMatrixSize (specialize' c (r₂ ◂ ps))
    ≤⟨ +-mono-≤ (specialize'-≤ c (r₁ ◂ ps)) (specialize'-≤ c (r₂ ◂ ps)) ⟩
      patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0
    <⟨ n<1+n _ ⟩
      suc (patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- specialize does not increase the pattern matrix size
  specialize-≤ : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0))
    → patternMatrixSize (specialize c P) ≤ patternMatrixSize P
  specialize-≤ c []       = ≤-refl
  specialize-≤ c (ps ∷ P) rewrite patternMatrixSize-◂◂ (specialize' c ps) (specialize c P)
    = +-mono-≤ (specialize'-≤ c ps) (specialize-≤ c P)

  specialize'-< : (c : NameCon d0) (ps : Patterns (TyData d0 ◂ αs0))
    → c ∈* ps
    → patternMatrixSize (specialize' c ps) < patternsSize ps 0
  specialize'-< c (con c' rs ◂ ps) c≡c' = lem (c ≟ c')
    where
      lem : (eq : Dec (c ≡ c'))
        → patternMatrixSize (specialize'ConCase c rs ps eq)
        < suc (patternsSize rs (patternsSize ps 0))
      lem (False ⟨ c≢c' ⟩) = contradiction c≡c' c≢c'
      lem (True ⟨ refl ⟩)
          rewrite patternsSize-◂◂ rs ps 0
          | +-identityʳ (patternsSize rs (patternsSize ps 0))
          = ≤-refl
  specialize'-< c (r₁ ∣ r₂ ◂ ps) (Left c∈r₁) =
    begin
      suc (patternMatrixSize (specialize' c (r₁ ◂ ps) ++ specialize' c (r₂ ◂ ps)))
    ≡⟨ cong suc (patternMatrixSize-◂◂ (specialize' c (r₁ ◂ ps)) (specialize' c (r₂ ◂ ps))) ⟩
      suc (patternMatrixSize (specialize' c (r₁ ◂ ps)) + patternMatrixSize (specialize' c (r₂ ◂ ps)))
    <⟨ s<s (+-mono-<-≤ (specialize'-< c (r₁ ◂ ps) c∈r₁) (specialize'-≤ c (r₂ ◂ ps))) ⟩
      suc (patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning
  specialize'-< c (r₁ ∣ r₂ ◂ ps) (Right c∈r₂) =
    begin
      suc (patternMatrixSize (specialize' c (r₁ ◂ ps) ++ specialize' c (r₂ ◂ ps)))
    ≡⟨ cong suc (patternMatrixSize-◂◂ (specialize' c (r₁ ◂ ps)) (specialize' c (r₂ ◂ ps))) ⟩
      suc (patternMatrixSize (specialize' c (r₁ ◂ ps)) + patternMatrixSize (specialize' c (r₂ ◂ ps)))
    <⟨ s<s (+-mono-≤-< (specialize'-≤ c (r₁ ◂ ps)) (specialize'-< c (r₂ ◂ ps) c∈r₂)) ⟩
      suc (patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- specialize strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
  specialize-< : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0))
    → c ∈** P
    → patternMatrixSize (specialize c P) < patternMatrixSize P
  specialize-< c (ps ∷ P) (here c∈ps)
    rewrite patternMatrixSize-◂◂ (specialize' c ps) (specialize c P)
    = +-mono-<-≤ (specialize'-< c ps c∈ps) (specialize-≤ c P)
  specialize-< c (ps ∷ P) (there c∈P)
    rewrite patternMatrixSize-◂◂ (specialize' c ps) (specialize c P)
    = +-mono-≤-< (specialize'-≤ c ps) (specialize-< c P c∈P)

  default'-≤ : (ps : Patterns (TyData d0 ◂ αs0)) → patternMatrixSize (default' ps) ≤ patternsSize ps 0
  default'-≤ (—       ◂ ps) rewrite +-identityʳ (patternsSize ps 0) = ≤-refl
  default'-≤ (con _ _ ◂ ps) = <⇒≤ 0<1+n
  default'-≤ (r₁ ∣ r₂ ◂ ps) =
    begin
      patternMatrixSize (default' (r₁ ◂ ps) ++ default' (r₂ ◂ ps))
    ≡⟨ patternMatrixSize-◂◂ (default' (r₁ ◂ ps)) (default' (r₂ ◂ ps)) ⟩
      patternMatrixSize (default' (r₁ ◂ ps)) + patternMatrixSize (default' (r₂ ◂ ps))
    ≤⟨ +-mono-≤ (default'-≤ (r₁ ◂ ps)) (default'-≤ (r₂ ◂ ps)) ⟩
      patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0
    <⟨ n<1+n _ ⟩
      suc (patternsSize (r₁ ◂ ps) 0 + patternsSize (r₂ ◂ ps) 0)
    ∎
    where open ≤-Reasoning

  -- default does not increase the pattern matrix size
  default-≤ : (P : PatternMatrix (TyData d0 ◂ αs0)) → patternMatrixSize (default_ P) ≤ patternMatrixSize P
  default-≤ []       = ≤-refl
  default-≤ (ps ∷ P) rewrite patternMatrixSize-◂◂ (default' ps) (default_ P)
    = +-mono-≤ (default'-≤ ps) (default-≤ P)

  Problem : Type
  Problem = Σ[ αs ∈ _ ] PatternMatrix αs × Patterns αs

  problemSize : Problem → Nat ×ₚ Nat
  problemSize (αs , (P , ps)) = (patternMatrixSize P + patternsSize ps 0) , lengthNat αs

  -- Lexicographic ordering on Problem
  _⊏_ : (P Q : Problem) → Type
  _⊏_ = ×-Lex _≡_ _<_ _<_ on problemSize

  -- _⊏_ is well-founded
  ⊏-wellFounded : WellFounded _⊏_
  ⊏-wellFounded = on-wellFounded problemSize (×-wellFounded <-wellFounded <-wellFounded)

  -- specialize strictly reduces the problem size
  specializeCon-⊏ : (P : PatternMatrix (TyData d0 ◂ αs0)) (c : NameCon d0) (rs : Patterns (argsTy (dataDefs sig d0) c)) (ps : Patterns αs0)
    → (_ , (specialize c P , rs ◂◂ᵖ ps)) ⊏ (_ , (P , con c rs ◂ ps))
  specializeCon-⊏ P c rs ps
    rewrite patternsSize-◂◂ rs ps 0
    = inj₁ (+-mono-≤-< (specialize-≤ c P) (n<1+n _))

  -- default strictly reduces the problem size
  default-⊏ : (P : PatternMatrix (TyData d0 ◂ αs0)) (qs : Patterns αs0)
    → (_ , (default_ P , qs)) ⊏ (_ , (P , — ◂ qs))
  default-⊏ P qs with m≤n⇒m<n∨m≡n (default-≤ P)
  ... | inj₁ defaultP<P = inj₁ (+-monoˡ-< (patternsSize qs 0) defaultP<P)
  ... | inj₂ defaultP≡P = inj₂ (cong (_+ patternsSize qs 0) defaultP≡P , n<1+n _)

  -- specialize strictly reduces the problem size if the constructor is in the first column of the matrix
  specializeWild-⊏ : (c : NameCon d0) (P : PatternMatrix (TyData d0 ◂ αs0)) (qs : Patterns αs0)
    → c ∈** P
    → (_ , (specialize c P , —* ◂◂ᵖ qs)) ⊏ (_ , (P , — ◂ qs))
  specializeWild-⊏ {d0} c P qs c∈P
    rewrite patternsSize-◂◂ (—* {αs = argsTy (dataDefs sig d0) c}) qs 0
    | patternsSize—* (argsTy (dataDefs sig d0) c) (patternsSize qs 0)
    = inj₁ (+-monoˡ-< (patternsSize qs 0) (specialize-< c P c∈P))

  -- Choosing the left pattern strictly reduces the problem size
  chooseOr-⊏ₗ : (P : PatternMatrix (α0 ◂ αs0)) (r₁ r₂ : Pattern α0) (ps : Patterns αs0)
    → (_ , (P , r₁ ◂ ps)) ⊏ (_ , (P , r₁ ∣ r₂ ◂ ps))
  chooseOr-⊏ₗ P r₁ r₂ ps =
    inj₁ (+-monoʳ-< (patternMatrixSize P) (m≤m+n (suc (patternsSize (r₁ ◂ ps) 0)) (patternsSize (r₂ ◂ ps) 0)))

  -- Choosing the right pattern strictly reduces the problem size
  chooseOr-⊏ᵣ : (P : PatternMatrix (α0 ◂ αs0)) (r₁ r₂ : Pattern α0) (ps : Patterns αs0)
    → (_ , (P , r₂ ◂ ps)) ⊏ (_ , (P , r₁ ∣ r₂ ◂ ps))
  chooseOr-⊏ᵣ P r₁ r₂ ps =
    inj₁ (+-monoʳ-< (patternMatrixSize P) (s<s (m≤n+m (patternsSize (r₂ ◂ ps) 0) (patternsSize (r₁ ◂ ps) 0))))

  ∀UsefulAcc' : (P : PatternMatrix αs0) (ps : Patterns αs0)
    → Acc _⊏_ (_ , (P , ps))
    → UsefulAcc P ps
  ∀UsefulAcc' P ⌈⌉ _ = done
  ∀UsefulAcc' {αs0 = TyData d ◂ αs0} P (— ◂ ps) (acc h) =
    step-wild
      (λ _ → ∀UsefulAcc' (default_ P) ps (h (default-⊏ P ps)))
      (λ c c∈P → ∀UsefulAcc' (specialize c P) (—* ◂◂ᵖ ps) (h (specializeWild-⊏ c P ps c∈P)))
  ∀UsefulAcc' P (con c rs ◂ ps) (acc h) =
    step-con (∀UsefulAcc' (specialize c P) (rs ◂◂ᵖ ps) (h (specializeCon-⊏ P c rs ps)))
  ∀UsefulAcc' P (r₁ ∣ r₂ ◂ ps) (acc h) =
    step-∣
      (∀UsefulAcc' P (r₁ ◂ ps) (h (chooseOr-⊏ₗ P r₁ r₂ ps)))
      (∀UsefulAcc' P (r₂ ◂ ps) (h (chooseOr-⊏ᵣ P r₁ r₂ ps)))

  ∀UsefulAcc : (P : PatternMatrix αs0) (ps : Patterns αs0) → UsefulAcc P ps
  ∀UsefulAcc P ps = ∀UsefulAcc' P ps (⊏-wellFounded _)

--------------------------------------------------------------------------------
-- Entrypoint

module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Type)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUsefulTerm : (pss : PatternMatrix αs) (ps : Patterns αs) → DecP (u pss ps)
  decUsefulTerm pss ps = decUseful (λ ⦃ sig' ⦄ → u ⦃ sig' ⦄) pss ps (∀UsefulAcc pss ps)
  {-# COMPILE AGDA2HS decUsefulTerm inline #-}
