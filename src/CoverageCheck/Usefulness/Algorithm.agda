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

TyStack : Type
TyStack = List Tys
{-# COMPILE AGDA2HS TyStack inline #-}

private
  variable
    αss βss : TyStack
    @0 αss0 βss0 : TyStack

module _ ⦃ @0 sig : Signature ⦄ where

  ValueStack : @0 TyStack → Type
  ValueStack αss = All Values αss
  {-# COMPILE AGDA2HS ValueStack inline #-}

  PatternStack : @0 TyStack → Type
  PatternStack αss = All Patterns αss
  {-# COMPILE AGDA2HS PatternStack inline #-}

  PatternMatrixStack : @0 TyStack → Type
  PatternMatrixStack αss = List (PatternStack αss)
  {-# COMPILE AGDA2HS PatternMatrixStack inline #-}


module _ ⦃ sig : Signature ⦄ {d : NameData} (c : NameCon d)
  (let αs = argsTy (dataDefs sig d) c)
  where

  -- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.

  specializeConCase : {c' : NameCon d}
    (let @0 αs' : Tys
         αs' = argsTy (dataDefs sig d) c')
    (rs : Patterns αs') (ps : Patterns βs0) (pss : PatternStack βss0)
    (eq : Dec (c ≡ c'))
    → PatternMatrixStack (αs ∷ βs0 ∷ βss0)
  specializeConCase rs ps pss eq =
    ifDec eq (λ where ⦃ refl ⦄ → (rs ∷ ps ∷ pss) ∷ []) []
  {-# COMPILE AGDA2HS specializeConCase inline #-}

  specialize' : PatternStack ((TyData d ∷ βs0) ∷ βss0) → PatternMatrixStack (αs ∷ βs0 ∷ βss0)
  specialize' ((—         ∷ ps) ∷ pss) = (—* ∷ ps ∷ pss) ∷ []
  specialize' ((con c' rs ∷ ps) ∷ pss) = specializeConCase rs ps pss (c ≟ c')
  specialize' ((r₁ ∣ r₂   ∷ ps) ∷ pss) = specialize' ((r₁ ∷ ps) ∷ pss) ++ specialize' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS specialize' #-}

  specialize : PatternMatrixStack ((TyData d ∷ βs0) ∷ βss0) → PatternMatrixStack (αs ∷ βs0 ∷ βss0)
  specialize = concatMap specialize'
  {-# COMPILE AGDA2HS specialize #-}


module _ ⦃ @0 sig : Signature ⦄ where

  rootConSet' : (p : Pattern (TyData d0)) → Set (NameCon d0)
  rootConSet' —         = Set.empty
  rootConSet' (con c _) = Set.singleton c
  rootConSet' (p ∣ q)   = Set.union (rootConSet' p) (rootConSet' q)
  {-# COMPILE AGDA2HS rootConSet' #-}

  rootConSet : (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)) → Set (NameCon d0)
  rootConSet psss = foldr (λ pss → Set.union (rootConSet' (headPattern (headAll pss)))) Set.empty psss
  {-# COMPILE AGDA2HS rootConSet #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Default matrix: filters out clauses whose first pattern is a constructor pattern
  default' : PatternStack ((α0 ∷ αs0) ∷ αss0) → PatternMatrixStack (αs0 ∷ αss0)
  default' ((—        ∷ ps) ∷ pss) = (ps ∷ pss) ∷ []
  default' ((con c rs ∷ ps) ∷ pss) = []
  default' ((r₁ ∣ r₂  ∷ ps) ∷ pss) = default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS default' #-}

  default_ : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0) → PatternMatrixStack (αs0 ∷ αss0)
  default_ = concatMap default'
  {-# COMPILE AGDA2HS default_ #-}


module Raw where

  module _ ⦃ sig : Signature ⦄ where

    -- Is there a constructor that does not appear in the first column of P?
    existMissCon : (P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)) → Bool
    existMissCon {d = d} psss = not (Set.null missConSet)
      where
        conSet missConSet : Set (NameCon d)
        conSet     = rootConSet psss
        missConSet = Set.difference (universalNameConSet (dataDefs sig d)) conSet
    {-# COMPILE AGDA2HS existMissCon #-}

    -- The core usefulness checking algorithm in the paper
    {-# TERMINATING #-}
    isUseful : (P : PatternMatrixStack αss) (pss : PatternStack αss) → Bool
    isUseful {[]} []      [] = True
    isUseful {[]} (_ ∷ _) [] = False
    isUseful {[] ∷ αss} psss (_ ∷ pss) = isUseful {αss} (map tailAll psss) pss
    isUseful {(TyData d ∷ αs) ∷ αss} psss ((— ∷ ps) ∷ pss) =
      if existMissCon psss
        then isUseful (default_ psss) (ps ∷ pss)
        else anyNameCon (dataDefs sig d) λ c → isUseful (specialize c psss) (—* ∷ ps ∷ pss)
    isUseful {(TyData d ∷ αs) ∷ αss} psss ((con c rs ∷ ps) ∷ pss) =
      isUseful (specialize c psss) (rs ∷ ps ∷ pss)
    isUseful {(TyData d ∷ αs) ∷ αss} psss ((r₁ ∣ r₂  ∷ ps) ∷ pss) =
      isUseful psss ((r₁ ∷ ps) ∷ pss) || isUseful psss ((r₂ ∷ ps) ∷ pss)
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

  _∈*_ _∉*_ : NameCon d0 → PatternStack ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈* pss = c ∈ headPattern (headAll pss)
  c ∉* pss = c ∉ headPattern (headAll pss)

  _∈**_ _∉**_ : NameCon d0 → PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈** psss = Any (c ∈*_) psss
  c ∉** psss = All (c ∉*_) psss


module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} (@0 c : NameCon d0) where

  memberRootConSet' : (p : Pattern (TyData d0))
    → Reflects (c ∈ p) (Set.member c (rootConSet' p))
  memberRootConSet' — rewrite prop-member-empty c = id
  memberRootConSet' (con c' _) rewrite prop-member-singleton c c' = isEquality c c'
  memberRootConSet' (p ∣ q)
    rewrite prop-member-union c (rootConSet' p) (rootConSet' q)
    = eitherReflects (memberRootConSet' p) (memberRootConSet' q)

  memberRootConSet : (psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (c ∈** psss) (Set.member c (rootConSet psss))
  memberRootConSet [] rewrite prop-member-empty c = λ ()
  memberRootConSet (pss ∷ psss)
    rewrite prop-member-union c (rootConSet' (headPattern (headAll pss))) (rootConSet psss)
    = mapReflects
        (either here there)
        (λ where (here h) → Left h; (there h) → Right h)
        (eitherReflects (memberRootConSet' (headPattern (headAll pss))) (memberRootConSet psss))


module @0 _ ⦃ @0 sig : Signature ⦄
  {@0 d0} (@0 c : NameCon d0) (@0 psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
  (let conSet     = rootConSet psss
       missConSet = Set.difference (universalNameConSet (dataDefs sig d0)) conSet)
  where

  notMemberMissConSet : Reflects (c ∈** psss) (not (Set.member c missConSet))
  notMemberMissConSet
    rewrite prop-member-difference c (universalNameConSet (dataDefs sig d0)) conSet
    | universalNameConSetUniversal (dataDefs sig d0) c
    | not-not (Set.member c conSet)
    = memberRootConSet c psss

  memberMissConSet : Reflects (c ∉** psss) (Set.member c missConSet)
  memberMissConSet rewrite sym (not-not (Set.member c missConSet)) =
    mapReflects (¬Any⇒All¬ _) All¬⇒¬Any (negReflects notMemberMissConSet)


module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} where

  nullRootConSet' : (p : Pattern (TyData d0))
    → Reflects (∀ c → c ∉ p) (Set.null (rootConSet' p))
  nullRootConSet' —
    rewrite prop-null-empty {NameCon d0} ⦃ iOrdNameIn ⦄
    = λ _ → id
  nullRootConSet' (con c _)
    rewrite prop-null-insert c Set.empty
    = λ h → h c refl
  nullRootConSet' (p ∣ q)
    rewrite prop-null-union (rootConSet' p) (rootConSet' q)
    = mapReflects
        {a = (∀ c → c ∉ p) × (∀ c → c ∉ q)}
        {b = (∀ c → c ∉ (p ∣ q))}
        (λ (h , h') c → either (h c) (h' c))
        (λ h → (λ c → h c ∘ Left) , (λ c → h c ∘ Right))
        (tupleReflects (nullRootConSet' p) (nullRootConSet' q))

  nullRootConSet : (psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (∀ c → c ∉** psss) (Set.null (rootConSet psss))
  nullRootConSet []
    rewrite prop-null-empty {NameCon d0} ⦃ iOrdNameIn ⦄
    = λ c → []
  nullRootConSet (pss ∷ psss)
    rewrite prop-null-union (rootConSet' (headPattern (headAll pss))) (rootConSet psss)
    = mapReflects
        {a = (∀ c → c ∉* pss) × (∀ c → c ∉** psss)}
        {b = (∀ c → c ∉** (pss ∷ psss))}
        (λ (h , h') c → h c ∷ h' c)
        (λ h → (λ c → headAll (h c)) , (λ c → tailAll (h c)))
        (tupleReflects (nullRootConSet' (headPattern (headAll pss))) (nullRootConSet psss))


module _ ⦃ sig : Signature ⦄ {d : NameData} where

  -- Are there constructors that does not appear in the first column of P?
  decExistMissCon : (P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0))
    → Either (Erase (∀ c → c ∈** P))
        (Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P)))
  decExistMissCon psss = case toAscNonEmptyW missConSet of λ where
      (Left (Erased empty)) →
        Left (Erased λ c → extractTrue ⦃ cong not (empty c) ⦄ (notMemberMissConSet c psss))
      (Right misses) → Right (if Set.null conSet
        then Left (Erased (extractTrue (nullRootConSet psss)))
        else Right (mapNonEmptyRefine (λ miss → extractTrue ⦃ miss ⦄ (memberMissConSet _ psss)) misses))
    where
      conSet missConSet : Set (NameCon d)
      conSet     = rootConSet psss
      missConSet = Set.difference (universalNameConSet (dataDefs sig d)) conSet
  {-# COMPILE AGDA2HS decExistMissCon #-}


record Usefulness
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αss0} (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0) → Type)
  : Type where
  field
    nilOkCase : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → u [] []

    @0 nilBadCase : ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 pss : PatternStack []} {@0 P : PatternMatrixStack []}
      → ¬ u (pss ∷ P) []

    tailCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 P : PatternMatrixStack ([] ∷ αss0)}
      {@0 pss : PatternStack αss0}
      → u (map tailAll P) pss
      → u P ([] ∷ pss)

    @0 tailCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 P : PatternMatrixStack ([] ∷ αss0)}
      {@0 pss : PatternStack αss0}
      → u P ([] ∷ pss)
      → u (map tailAll P) pss

    orCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
      {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → These (u P ((r₁ ∷ ps) ∷ pss)) (u P ((r₂ ∷ ps) ∷ pss))
      → u P ((r₁ ∣ r₂ ∷ ps) ∷ pss)

    @0 orCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
      {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → u P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
      → These (u P ((r₁ ∷ ps) ∷ pss)) (u P ((r₂ ∷ ps) ∷ pss))

    conCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {c : NameCon d}
      {@0 P : PatternMatrixStack ((TyData d ∷ βs0) ∷ αss0)}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0} {@0 pss : PatternStack αss0}
      → u (specialize c P) (rs ∷ ps ∷ pss)
      → u P ((con c rs ∷ ps) ∷ pss)

    @0 conCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {c : NameCon d}
      {@0 P : PatternMatrixStack ((TyData d ∷ βs0) ∷ αss0)}
      (let αs = argsTy (dataDefs sig d) c)
      {@0 rs : Patterns αs} {@0 ps : Patterns βs0} {@0 pss : PatternStack αss0}
      → u P ((con c rs ∷ ps) ∷ pss)
      → u (specialize c P) (rs ∷ ps ∷ pss)

    wildMissCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
      {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
      → u (default_ P) (ps ∷ pss)
      → u P ((— ∷ ps) ∷ pss)

    @0 wildMissCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
      {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
      → u P ((— ∷ ps) ∷ pss)
      → u (default_ P) (ps ∷ pss)

    wildCompCase : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
      {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → @0 (∀ c → c ∈** P)
      → NonEmpty (Σ[ c ∈ NameCon d ] u (specialize c P) (—* ∷ ps ∷ pss))
      → u P ((— ∷ ps) ∷ pss)

    @0 wildCompCaseInv : ∀ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      {d} {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
      {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
      → @0 (∀ c → c ∈** P)
      → u P ((— ∷ ps) ∷ pss)
      → NonEmpty (Σ[ c ∈ NameCon d ] u (specialize c P) (—* ∷ ps ∷ pss))

open Usefulness ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Usefulness class #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Specialized accessibility predicate for usefulness checking algorithm
  -- for separating termination proof from the algorithm
  -- This method is due to Ana Bove 2003.
  data @0 UsefulAcc : (P : PatternMatrixStack αss) (ps : PatternStack αss) → Type where
    done : {P : PatternMatrixStack []} → UsefulAcc P []

    step-tail : {P : PatternMatrixStack ([] ∷ αss)} {pss : PatternStack αss}
      → UsefulAcc (map tailAll P) pss
      → UsefulAcc P ([] ∷ pss)

    step-wild : {P : PatternMatrixStack ((TyData d ∷ αs) ∷ αss)}
      {ps : Patterns αs} {pss : PatternStack αss}
      → (Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
          → UsefulAcc (default_ P) (ps ∷ pss))
      → (∀ c → c ∈** P → UsefulAcc (specialize c P) (—* ∷ ps ∷ pss))
      → UsefulAcc P ((— ∷ ps) ∷ pss)

    step-con : {P : PatternMatrixStack ((TyData d ∷ βs) ∷ αss)} {c : NameCon d}
      (let αs = argsTy (dataDefs sig d) c)
      {rs : Patterns αs} {ps : Patterns βs} {pss : PatternStack αss}
      → UsefulAcc (specialize c P) (rs ∷ ps ∷ pss)
      → UsefulAcc P ((con c rs ∷ ps) ∷ pss)

    step-∣ : {P : PatternMatrixStack ((α ∷ αs) ∷ αss)}
      {p q : Pattern α} {ps : Patterns αs} {pss : PatternStack αss}
      → UsefulAcc P ((p ∷ ps) ∷ pss)
      → UsefulAcc P ((q ∷ ps) ∷ pss)
      → UsefulAcc P ((p ∣ q ∷ ps) ∷ pss)


module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αss0} (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0) → Type)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful' : (P : PatternMatrixStack αss) (ps : PatternStack αss)
    → @0 UsefulAcc P ps
    → DecP (u P ps)
  decUseful' {[]} []      [] done = Yes nilOkCase
  decUseful' {[]} (_ ∷ _) [] done = No nilBadCase
  decUseful' {[] ∷ αss} psss ([] ∷ pss) (step-tail h) =
    mapDecP tailCase tailCaseInv
      (decUseful' (map tailAll psss) pss h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((— ∷ ps) ∷ pss) (step-wild h h') =
    case decExistMissCon psss of λ where
      (Right miss) →
        mapDecP (wildMissCase miss) (wildMissCaseInv miss)
          (decUseful' (default_ psss) (ps ∷ pss) (h miss))
      (Left (Erased comp)) →
        mapDecP (wildCompCase comp) (wildCompCaseInv comp)
          (decPAnyNameCon (dataDefs sig d) λ c →
            decUseful' (specialize c psss) (—* ∷ ps ∷ pss) (h' c (comp c)))
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((con c rs ∷ ps) ∷ pss) (step-con h) =
    mapDecP conCase conCaseInv
      (decUseful' (specialize c psss) (rs ∷ ps ∷ pss) h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((r₁ ∣ r₂ ∷ ps) ∷ pss) (step-∣ h h') =
    mapDecP orCase orCaseInv
      (theseDecP (decUseful' psss ((r₁ ∷ ps) ∷ pss) h) (decUseful' psss ((r₂ ∷ ps) ∷ pss) h'))
  {-# COMPILE AGDA2HS decUseful' #-}

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
  open import Data.Product using () renaming (_×_ to Product; _,_ to infix -1 _,_)
  open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
  open import Data.Sum using (inj₁; inj₂)
  open import Function.Base using (_on_)
  open import Induction.WellFounded using (WellFounded; Acc; acc)
  open import Relation.Binary.Construct.On using () renaming (wellFounded to on-wellFounded)

  patternsSize : Patterns αs0 → Nat → Nat
  patternsSize []              n = n
  patternsSize (—        ∷ ps) n = patternsSize ps n
  patternsSize (con c rs ∷ ps) n = suc (patternsSize rs (patternsSize ps n))
  patternsSize (r₁ ∣ r₂  ∷ ps) n = suc (patternsSize (r₁ ∷ ps) n + patternsSize (r₂ ∷ ps) n)

  patternStackSize : PatternStack αss0 → Nat → Nat
  patternStackSize []         n = n
  patternStackSize (ps ∷ pss) n = patternsSize ps (patternStackSize pss n)

  patternMatrixStackSize : PatternMatrixStack αss0 → Nat
  patternMatrixStackSize P = sum (map (flip patternStackSize 0) P)

  patternsSize—* : ∀ αs n → patternsSize (—* {αs = αs}) n ≡ n
  patternsSize—* []       n = refl
  patternsSize—* (α ∷ αs) n = patternsSize—* αs n

  sum-++ : (xs ys : List Nat) → sum (xs ++ ys) ≡ sum xs + sum ys
  sum-++ []       ys = refl
  sum-++ (x ∷ xs) ys rewrite sum-++ xs ys = sym (+-assoc x (sum xs) (sum ys))

  patternMatrixStackSize-++ : (P Q : PatternMatrixStack αss0) → patternMatrixStackSize (P ++ Q) ≡ patternMatrixStackSize P + patternMatrixStackSize Q
  patternMatrixStackSize-++ P Q
    rewrite map-++ (flip patternStackSize 0) P Q
    | sum-++ (map (flip patternStackSize 0) P) (map (flip patternStackSize 0) Q)
    = refl

  tail-≡ : (P : PatternMatrixStack ([] ∷ αss0))
    → patternMatrixStackSize (map tailAll P) ≡ patternMatrixStackSize P
  tail-≡ []               = refl
  tail-≡ (([] ∷ pss) ∷ P) = cong (_ +_) (tail-≡ P)

  specialize'-≤ : (c : NameCon d0) (pss : PatternStack ((TyData d0 ∷ αs0) ∷ αss0))
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
  specialize-≤ : (c : NameCon d0) (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → patternMatrixStackSize (specialize c P) ≤ patternMatrixStackSize P
  specialize-≤ c []       = ≤-refl
  specialize-≤ c (ps ∷ P) rewrite patternMatrixStackSize-++ (specialize' c ps) (specialize c P)
    = +-mono-≤ (specialize'-≤ c ps) (specialize-≤ c P)

  specialize'-< : (c : NameCon d0) (pss : PatternStack ((TyData d0 ∷ αs0) ∷ αss0))
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
  specialize-< : (c : NameCon d0) (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → c ∈** P
    → patternMatrixStackSize (specialize c P) < patternMatrixStackSize P
  specialize-< c (pss ∷ P) (here h)
    rewrite patternMatrixStackSize-++ (specialize' c pss) (specialize c P)
    = +-mono-<-≤ (specialize'-< c pss h) (specialize-≤ c P)
  specialize-< c (pss ∷ P) (there h)
    rewrite patternMatrixStackSize-++ (specialize' c pss) (specialize c P)
    = +-mono-≤-< (specialize'-≤ c pss) (specialize-< c P h)

  default'-≤ : (pss : PatternStack ((TyData d0 ∷ αs0) ∷ αss0))
    → patternMatrixStackSize (default' pss)
    ≤ patternStackSize pss 0
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
  default-≤ : (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → patternMatrixStackSize (default_ P) ≤ patternMatrixStackSize P
  default-≤ [] = ≤-refl
  default-≤ (ps ∷ P) rewrite patternMatrixStackSize-++ (default' ps) (default_ P)
    = +-mono-≤ (default'-≤ ps) (default-≤ P)

  Problem : Type
  Problem = Σ[ αss ∈ _ ] PatternMatrixStack αss × PatternStack αss

  problemSize : Problem → Product Nat (Product Nat Nat)
  problemSize (αss , (P , ps)) =
    (patternMatrixStackSize P + patternStackSize ps 0) ,
    (sum (map lengthNat αss) ,
    lengthNat αss)

  -- Lexicographic ordering on Problem
  _⊏_ : (P Q : Problem) → Type
  _⊏_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_) on problemSize

  -- _⊏_ is well-founded
  ⊏-wellFounded : WellFounded _⊏_
  ⊏-wellFounded = on-wellFounded problemSize (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded))

  tail-⊏ : (P : PatternMatrixStack ([] ∷ αss0)) (pss : PatternStack αss0)
    → (_ , (map tailAll P , pss)) ⊏ (_ , (P , [] ∷ pss))
  tail-⊏ P pss =
    inj₂ (cong (_+ patternStackSize pss 0) (tail-≡ P) , (inj₂ (refl , ≤-refl)))

  -- specialize strictly reduces the problem size
  specializeCon-⊏ : (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    (c : NameCon d0) (rs : Patterns (argsTy (dataDefs sig d0) c)) (ps : Patterns αs0) (pss : PatternStack αss0)
    → (_ , (specialize c P , rs ∷ ps ∷ pss)) ⊏ (_ , (P , (con c rs ∷ ps) ∷ pss))
  specializeCon-⊏ P c rs ps pss =
    inj₁ (+-mono-≤-< (specialize-≤ c P) (n<1+n _))

  -- default strictly reduces the problem size
  default-⊏ : (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    (qs : Patterns αs0) (pss : PatternStack αss0)
    → (_ , (default_ P , qs ∷ pss)) ⊏ (_ , (P , (— ∷ qs) ∷ pss))
  default-⊏ P qs pss with m≤n⇒m<n∨m≡n (default-≤ P)
  ... | inj₁ h = inj₁ (+-monoˡ-< (patternStackSize (qs ∷ pss) 0) h)
  ... | inj₂ h = inj₂ (cong (_+ patternStackSize (qs ∷ pss) 0) h , inj₁ (n<1+n _))

  -- specialize strictly reduces the problem size if the constructor is in the first column of the matrix
  specializeWild-⊏ : (c : NameCon d0) (P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    (qs : Patterns αs0) (pss : PatternStack αss0)
    → c ∈** P
    → (_ , (specialize c P , —* ∷ qs ∷ pss)) ⊏ (_ , (P , (— ∷ qs) ∷ pss))
  specializeWild-⊏ {d0} c P qs pss h
    rewrite patternsSize—* (argsTy (dataDefs sig d0) c) (patternStackSize (qs ∷ pss) 0)
    = inj₁ (+-monoˡ-< (patternStackSize (qs ∷ pss) 0) (specialize-< c P h))

  -- Choosing the left pattern strictly reduces the problem size
  chooseOr-⊏ₗ : (P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0))
    (r₁ r₂ : Pattern α0) (ps : Patterns αs0) (pss : PatternStack αss0)
    → (_ , (P , (r₁ ∷ ps) ∷ pss)) ⊏ (_ , (P , ((r₁ ∣ r₂) ∷ ps) ∷ pss))
  chooseOr-⊏ₗ P r₁ r₂ ps pss =
    inj₁ (+-monoʳ-< (patternMatrixStackSize P) (m≤m+n (suc (patternStackSize ((r₁ ∷ ps) ∷ pss) 0)) (patternStackSize ((r₂ ∷ ps) ∷ pss) 0)))

  -- Choosing the right pattern strictly reduces the problem size
  chooseOr-⊏ᵣ : (P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0))
    (r₁ r₂ : Pattern α0) (ps : Patterns αs0) (pss : PatternStack αss0)
    → (_ , (P , (r₂ ∷ ps) ∷ pss)) ⊏ (_ , (P , ((r₁ ∣ r₂) ∷ ps) ∷ pss))
  chooseOr-⊏ᵣ P r₁ r₂ ps pss =
    inj₁ (+-monoʳ-< (patternMatrixStackSize P) (s<s (m≤n+m (patternStackSize ((r₂ ∷ ps) ∷ pss) 0) (patternStackSize ((r₁ ∷ ps) ∷ pss) 0))))

  ∀UsefulAcc' : (P : PatternMatrixStack αss0) (pss : PatternStack αss0)
    → Acc _⊏_ (_ , (P , pss))
    → UsefulAcc P pss
  ∀UsefulAcc' P [] (acc h) = done
  ∀UsefulAcc' P ([] ∷ pss) (acc h) =
    step-tail (∀UsefulAcc' (map tailAll P) pss (h (tail-⊏ P pss)))
  ∀UsefulAcc' {αss0 = (TyData d ∷ αs0) ∷ αss0} P ((— ∷ ps) ∷ pss) (acc h) =
    step-wild
      (λ _ → ∀UsefulAcc' (default_ P) (ps ∷ pss) (h (default-⊏ P ps pss)))
      (λ c m → ∀UsefulAcc' (specialize c P) (—* ∷ ps ∷ pss) (h (specializeWild-⊏ c P ps pss m)))
  ∀UsefulAcc' P ((con c rs ∷ ps) ∷ pss) (acc h) =
    step-con (∀UsefulAcc' (specialize c P) (rs ∷ ps ∷ pss) (h (specializeCon-⊏ P c rs ps pss)))
  ∀UsefulAcc' P ((r₁ ∣ r₂ ∷ ps) ∷ pss) (acc h) =
    step-∣
      (∀UsefulAcc' P ((r₁ ∷ ps) ∷ pss) (h (chooseOr-⊏ₗ P r₁ r₂ ps pss)))
      (∀UsefulAcc' P ((r₂ ∷ ps) ∷ pss) (h (chooseOr-⊏ᵣ P r₁ r₂ ps pss)))


  ∀UsefulAcc : (P : PatternMatrixStack αss0) (ps : PatternStack αss0) → UsefulAcc P ps
  ∀UsefulAcc P ps = ∀UsefulAcc' P ps (⊏-wellFounded _)

--------------------------------------------------------------------------------
-- Entrypoint

module _
  (u : ∀ ⦃ @0 sig : Signature ⦄ {@0 αss0} (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0) → Type)
  ⦃ _ : Usefulness u ⦄
  ⦃ sig : Signature ⦄
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful : (pss : PatternMatrix αs) (ps : Patterns αs)
    → DecP (u (map (_∷ []) pss) (ps ∷ []))
  decUseful pss ps =
    decUseful' (λ ⦃ sig' ⦄ → u ⦃ sig' ⦄) (map (_∷ []) pss) (ps ∷ []) (∀UsefulAcc _ _)
  {-# COMPILE AGDA2HS decUseful #-}
