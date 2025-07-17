module Exhaustiveness where

open import Data.Bool.Base using (true; false; _∧_)
open import Data.Fin.Base as Fin using (zero; suc)
import Data.Fin.Properties as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Properties using (sum-++; map-++; ++-identityʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using (¬All⇒Any¬; All¬⇒¬Any; ¬Any⇒All¬)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties as Any using (¬Any[])
open import Data.List.Relation.Unary.First as First using (First; toAny)
open import Data.List.Relation.Unary.First.Properties as First using (All⇒¬First)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _≤_; _<_)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product.Base as Product using (∃-syntax; _×_; -,_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (id; _∘_; flip; _on_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Induction.WellFounded using (WellFounded; Acc; acc)
import Relation.Binary.Construct.On as On
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; ≢-sym; cong; cong₂)
open import Relation.Nullary.Decidable as Dec using (Dec; _because_; yes; no; ¬?; _⊎-dec_; _×-dec_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Negation.Core using (¬_; contradiction; contraposition)

open import Extra
open import Pattern

private
  variable
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------
-- Exhaustiveness and usefulness

-- There is a matching row in P for every list of values
Exhaustive : PatMat αs → Set
Exhaustive P = ∀ vs → Match P vs

-- There is a list of values that does not match any row in P
NonExhaustive : PatMat αs → Set
NonExhaustive P = ∃[ vs ] ¬ Match P vs

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
Useful : PatMat αs → Pats αs → Set
Useful P ps = ∃[ vs ] P ⋠** vs × ps ≼* vs

-- non-exhaustiveness defined in terms of usefulness:
-- P is non-exhaustive if ∙* is useful with respect to P
NonExhaustive′ : PatMat αs → Set
NonExhaustive′ P = Useful P ∙*

-- P is exhaustive if ∙* is not useful with respect to P
Exhaustive′ : PatMat αs → Set
Exhaustive′ P = ¬ NonExhaustive′ P

module _ {P : PatMat αs} where

  NonExhaustive′→NonExhaustive : NonExhaustive′ P → NonExhaustive P
  NonExhaustive′→NonExhaustive (vs , ∙*ps⋠vs , _) = vs , contraposition toAny ∙*ps⋠vs

  NonExhaustive→NonExhaustive′ : NonExhaustive P → NonExhaustive′ P
  NonExhaustive→NonExhaustive′ (vs , P⋠vs) = vs , ¬First⇒¬Any id P⋠vs , ∙*≼

  -- The two definitions of non-exhaustiveness are equivalent
  NonExhaustive′⇔NonExhaustive : NonExhaustive′ P ⇔ NonExhaustive P
  NonExhaustive′⇔NonExhaustive = mk⇔ NonExhaustive′→NonExhaustive NonExhaustive→NonExhaustive′

  Exhaustive→Exhaustive′ : Exhaustive P → Exhaustive′ P
  Exhaustive→Exhaustive′ exh (vs , P⋠vs , _) = P⋠vs (toAny (exh vs))

  Exhaustive′→Exhaustive : Exhaustive′ P → Exhaustive P
  Exhaustive′→Exhaustive exh vs with match? P vs
  ... | true because [P≼vs] = invert [P≼vs]
  ... | false because [P⋠vs] = contradiction (vs , ¬First⇒¬Any id (invert [P⋠vs]) , ∙*≼) exh

  -- The two definitions of exhaustiveness are equivalent
  Exhaustive′⇔Exhaustive : Exhaustive′ P ⇔ Exhaustive P
  Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

--------------------------------------------------------------------------------
-- Operations on patterns used in the algorithm

infix 4 _∈_ _∉_ _∈?_ _∉?_

-- Does c appear in p?
_∈_ : Con α → Pat α → Set
c ∈ ∙ = ⊥
c ∈ con c′ _ = c ≡ c′
c ∈ (p ∣ q) = c ∈ p ⊎ c ∈ q

_∉_ : Con α → Pat α → Set
c ∉ p = ¬ c ∈ p

_∈?_ : (c : Con α) (p : Pat α) → Dec (c ∈ p)
c ∈? ∙ = no id
c ∈? con c′ _ = c Fin.≟ c′
c ∈? (p ∣ q) = c ∈? p ⊎-dec c ∈? q

_∉?_ : (c : Con α) (p : Pat α) → Dec (c ∉ p)
c ∉? p = ¬? (c ∈? p)

-- Is p empty?
empty? : (p : Pat α) → Dec (∀ c → c ∉ p)
empty? ∙ = yes λ c → id
empty? (con c _) = no λ h → h c refl
empty? (p ∣ q) =
  Dec.map′
    (λ (h , h′) c → [ h c , h′ c ])
    (λ h → (λ c → h c ∘ inj₁) , (λ c → h c ∘ inj₂))
    (empty? p ×-dec empty? q)

-- Predicate on pattern matrix P that states if the first column of P
-- covers all constructor or there is a missing constructor.
Complete Missing : PatMat (α ∷ αs) → Set
Complete P = ∀ c → Any (λ ps → c ∈ All.head ps) P
Missing P = ∃[ c ] All (λ ps → c ∉ All.head ps) P

-- Is the set of root constructors that appear in the first column of P empty?
rootConsEmpty? : (P : PatMat (α ∷ αs))
  → Dec (∀ c → All (λ ps → c ∉ All.head ps) P)
rootConsEmpty? [] = yes λ _ → []
rootConsEmpty? (ps ∷ P) =
  Dec.map′
    (λ (h , h′) c → h c ∷ h′ c)
    (λ h → All.head ∘ h , All.tail ∘ h)
    (empty? (All.head ps) ×-dec rootConsEmpty? P)

-- Is there a constructor that does not appear in the first column of P?
∃missingCon? : (P : PatMat (α ∷ αs)) → Missing P ⊎ Complete P
∃missingCon? {α} P with rootConsEmpty? P
... | true because [empty] = inj₁ (inhabCon α , invert [empty] (inhabCon α))
... | no _ with allOrCounterexample (λ c → Any.any? (λ ps → c ∈? All.head ps) P)
...   | inj₁ ∀c∈P = inj₂ ∀c∈P
...   | inj₂ (c , c∉P) = inj₁ (c , ¬Any⇒All¬ P c∉P)

-- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.
𝒮-aux : (c : Con α) → Pats (α ∷ αs) → PatMat (argsTy α c ++ αs)
𝒮-aux c (∙ ∷ ps) = (∙* ++ₚ ps) ∷ []
𝒮-aux c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = (rs ++ₚ ps) ∷ []
𝒮-aux c (r₁ ∣ r₂ ∷ ps) = 𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)

𝒮 : (c : Con α) → PatMat (α ∷ αs) → PatMat (argsTy α c ++ αs)
𝒮 = List.concatMap ∘ 𝒮-aux

-- Default matrix: filters out clauses whose first pattern is a constructor pattern
𝒟-aux : Pats (α ∷ αs) → PatMat αs
𝒟-aux (∙ ∷ ps) = ps ∷ []
𝒟-aux (con _ _ ∷ ps) = []
𝒟-aux (r₁ ∣ r₂ ∷ ps) = 𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps)

𝒟 : PatMat (α ∷ αs) → PatMat αs
𝒟 = List.concatMap 𝒟-aux

--------------------------------------------------------------------------------
-- Properties of ≼ and 𝒮/𝒟

module _ {c : Con α} {us : Vals (argsTy α c)} {vs : Vals αs} where

  𝒮-aux-preserves-≼ : {ps : Pats (α ∷ αs)}
    → ps ≼* con {α} c us ∷ vs
    → 𝒮-aux c ps ≼** (us ++ᵥ vs)
  𝒮-aux-preserves-≼ {∙ ∷ ps} ∙ps≼cusvs = here (∙≼*⁻ ∙ps≼cusvs)
  𝒮-aux-preserves-≼ {con d rs ∷ ps} drsps≼cusvs with c Fin.≟ d
  ... | no c≢d = contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c≢d
  ... | yes refl = here (con≼*⁻ drsps≼cusvs)
  𝒮-aux-preserves-≼ {r₁ ∣ r₂ ∷ ps} =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map 𝒮-aux-preserves-≼ 𝒮-aux-preserves-≼ ∘
    ∣≼*⁻

  -- 𝒮 preserves ≼
  𝒮-preserves-≼ : {P : PatMat (α ∷ αs)}
    → P ≼** con {α} c us ∷ vs
    → 𝒮 c P ≼** (us ++ᵥ vs)
  𝒮-preserves-≼ = Any.concat⁺ ∘ Any.gmap 𝒮-aux-preserves-≼

  𝒮-aux-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
    → 𝒮-aux c ps ≼** (us ++ᵥ vs)
    → ps ≼* con {α} c us ∷ vs
  𝒮-aux-preserves-≼⁻ {∙ ∷ ps} (here ∙*ps≼usvs) = ∙≼*⁺ ∙*ps≼usvs
  𝒮-aux-preserves-≼⁻ {con d rs ∷ ps} _ with c Fin.≟ d
  𝒮-aux-preserves-≼⁻ {con d rs ∷ ps} (here drsps≼cusvs) | yes refl = con≼*⁺ drsps≼cusvs
  𝒮-aux-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map 𝒮-aux-preserves-≼⁻ 𝒮-aux-preserves-≼⁻ ∘ Any.++⁻ _

  -- Unspecialization preserves ≼
  𝒮-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
    → 𝒮 c P ≼** (us ++ᵥ vs)
    → P ≼** con {α} c us ∷ vs
  𝒮-preserves-≼⁻ = Any.map 𝒮-aux-preserves-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

  𝒮-preserves-≼⇔ : {P : PatMat (α ∷ αs)}
    → P ≼** con {α} c us ∷ vs ⇔ 𝒮 c P ≼** (us ++ᵥ vs)
  𝒮-preserves-≼⇔ = mk⇔ 𝒮-preserves-≼ 𝒮-preserves-≼⁻


module _ {c : Con α} {us : Vals (argsTy α c)} {vs : Vals αs} where

  𝒟-aux-preserves-≼ : {ps : Pats (α ∷ αs)}
    → c ∉ All.head ps
    → ps ≼* con {α} c us ∷ vs
    → 𝒟-aux ps ≼** vs
  𝒟-aux-preserves-≼ {∙ ∷ ps} _ ∙ps≼cusvs = here (∷⁻ ∙ps≼cusvs .proj₂)
  𝒟-aux-preserves-≼ {con d rs ∷ ps} c∉d drsps≼cusvs =
    contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c∉d
  𝒟-aux-preserves-≼ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map
      (𝒟-aux-preserves-≼ (c∉r₁∪r₂ ∘ inj₁))
      (𝒟-aux-preserves-≼ (c∉r₁∪r₂ ∘ inj₂)) ∘
    ∣≼*⁻

  -- If c does not appear in the first column of P, 𝒟 preserves ≼
  𝒟-preserves-≼ : {P : PatMat (α ∷ αs)}
    → All (λ ps → c ∉ All.head ps) P
    → P ≼** con {α} c us ∷ vs
    → 𝒟 P ≼** vs
  𝒟-preserves-≼ {ps ∷ P} (c∉ps ∷ _) (here ps≼cusvs) =
    Any.++⁺ˡ (𝒟-aux-preserves-≼ c∉ps ps≼cusvs)
  𝒟-preserves-≼ {ps ∷ P} (_ ∷ c∉P) (there P≼cusvs) =
    Any.++⁺ʳ _ (𝒟-preserves-≼ c∉P P≼cusvs)


module _ {v : Val α} {vs : Vals αs} where

  𝒟-aux-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
    → 𝒟-aux ps ≼** vs
    → ps ≼* v ∷ vs
  𝒟-aux-preserves-≼⁻ {∙ ∷ ps} (here ∙ps≼vvs) = ∙≼ ∷ ∙ps≼vvs
  𝒟-aux-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map 𝒟-aux-preserves-≼⁻ 𝒟-aux-preserves-≼⁻ ∘ Any.++⁻ _

  𝒟-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
    → 𝒟 P ≼** vs
    → P ≼** v ∷ vs
  𝒟-preserves-≼⁻ = Any.map 𝒟-aux-preserves-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

--------------------------------------------------------------------------------
-- Properties of usefulness

-- [] is useful wrt []
useful-[]-[] : Useful [] []
useful-[]-[] = [] , (λ ()) , []

-- [] is not wrt any non-empty matrix
¬useful-∷-[] : {ps : Pats []} {P : PatMat []} → ¬ Useful (ps ∷ P) []
¬useful-∷-[] {[]} ([] , []P⋠[] , _) = []P⋠[] (here [])

module _ {P : PatMat (α ∷ αs)} {r₁ r₂ : Pat α} {ps : Pats αs} where

  merge-useful : Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps) → Useful P (r₁ ∣ r₂ ∷ ps)
  merge-useful (inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)) =
    vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs
  merge-useful (inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)) =
    vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs

  merge-useful⁻ : Useful P (r₁ ∣ r₂ ∷ ps) → Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)
  merge-useful⁻ (vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs) =
    inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)
  merge-useful⁻ (vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs) =
    inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)

  -- (r₁ ∣ r₂ ∷ ps) is useful wrt P iff (r₁ ∷ ps) or (r₂ ∷ ps) is useful wrt P
  merge-useful⇔ : (Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)) ⇔ Useful P (r₁ ∣ r₂ ∷ ps)
  merge-useful⇔ = mk⇔ merge-useful merge-useful⁻


module _ {P : PatMat (α ∷ αs)} {c : Con α} {rs : Pats (argsTy α c)} {ps : Pats αs} where

  𝒮-preserves-usefulness-con :
      Useful P (con c rs ∷ ps)
    → Useful (𝒮 c P) (All.++⁺ rs ps)
  𝒮-preserves-usefulness-con (con c vs ∷ us , P⋠cvsus , con≼ rs≼vs ∷ ps≼us) =
    All.++⁺ vs us , contraposition 𝒮-preserves-≼⁻ P⋠cvsus , ++⁺ rs≼vs ps≼us

  𝒮-preserves-usefulness-con⁻ :
      Useful (𝒮 c P) (All.++⁺ rs ps)
    → Useful P (con c rs ∷ ps)
  𝒮-preserves-usefulness-con⁻ (usvs , 𝒮P⋠usvs , rsps≼usvs)
    with us , vs , refl , rs≼us , ps≼vs ← split rs rsps≼usvs =
    con c us ∷ vs , contraposition 𝒮-preserves-≼ 𝒮P⋠usvs , con≼ rs≼us ∷ ps≼vs

  -- con c rs ∷ ps is useful wrt P iff rs ++ ps is useful wrt 𝒮 c P
  𝒮-preserves-usefulness-con⇔ :
      Useful (𝒮 c P) (All.++⁺ rs ps)
    ⇔ Useful P (con c rs ∷ ps)
  𝒮-preserves-usefulness-con⇔ =
    mk⇔ 𝒮-preserves-usefulness-con⁻ 𝒮-preserves-usefulness-con


module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c P`
  ∃𝒮-preserves-usefulness-∙ :
      Useful P (∙ ∷ ps)
    → ∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps)
  ∃𝒮-preserves-usefulness-∙ (con c us ∷ vs , P⋠cusvs , ∙≼ ∷ ps≼vs) =
    c , All.++⁺ us vs , contraposition 𝒮-preserves-≼⁻ P⋠cusvs , ++⁺ ∙*≼ ps≼vs

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c P`, `∙ ∷ ps` is also useful wrt P
  ∃𝒮-preserves-usefulness-∙⁻ :
      ∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps)
    → Useful P (∙ ∷ ps)
  ∃𝒮-preserves-usefulness-∙⁻ (c , usvs , 𝒮P⋠usvs , ∙*ps≼usvs)
    with us , vs , refl , _ , ps≼vs ← split {argsTy α c} ∙* ∙*ps≼usvs =
    con c us ∷ vs , contraposition 𝒮-preserves-≼ 𝒮P⋠usvs , ∙≼ ∷ ps≼vs

  -- ∙ ∷ ps is useful wrt P iff ∙* ++ ps is useful wrt 𝒮 c P
  ∃𝒮-preserves-usefulness-∙⇔ :
      (∃[ c ] Useful (𝒮 c P) (All.++⁺ ∙* ps))
    ⇔ Useful P (∙ ∷ ps)
  ∃𝒮-preserves-usefulness-∙⇔ =
    mk⇔ ∃𝒮-preserves-usefulness-∙⁻ ∃𝒮-preserves-usefulness-∙


module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

  -- ps is useful wrt (𝒟 P) if (∙ ∷ ps) is useful wrt P
  𝒟-preserves-usefulness : Useful P (∙ ∷ ps) → Useful (𝒟 P) ps
  𝒟-preserves-usefulness (v ∷ vs  , P⋠vvs , ∙≼ ∷ ps≼vs) =
    vs , contraposition 𝒟-preserves-≼⁻ P⋠vvs , ps≼vs

  -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt 𝒟 P, ∙ ∷ ps is also useful wrt P.
  𝒟-preserves-usefulness⁻ : Missing P → Useful (𝒟 P) ps → Useful P (∙ ∷ ps)
  𝒟-preserves-usefulness⁻ (c , c∉P) (vs , 𝒟P⋠vs , ps≼vs) =
    inhabOf c ∷ vs , contraposition (𝒟-preserves-≼ c∉P) 𝒟P⋠vs , ∙≼ ∷ ps≼vs

  𝒟-preserves-usefulness⇔ : Missing P → Useful (𝒟 P) ps ⇔ Useful P (∙ ∷ ps)
  𝒟-preserves-usefulness⇔ ∃c∉P =
    mk⇔ (𝒟-preserves-usefulness⁻ ∃c∉P) 𝒟-preserves-usefulness

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

-- Specialized accessibility predicate for usefulness checking algorithm
-- for separating termination proof from the algorithm
-- This method is due to Ana Bove 2003.
data UsefulAcc : (P : PatMat αs) (ps : Pats αs) → Set where
  done : {P : PatMat []} → UsefulAcc P []

  step-∙ : {P : PatMat (α ∷ αs)} {ps : Pats αs}
    → (Missing P → UsefulAcc (𝒟 P) ps)
    → (∀ c → Any (λ qs → c ∈ All.head qs) P → UsefulAcc (𝒮 c P) (All.++⁺ ∙* ps))
    → UsefulAcc P (∙ ∷ ps)

  step-con : {P : PatMat (α ∷ αs)} {c : Con α} {rs : Pats (argsTy α c)} {ps : Pats αs}
    → UsefulAcc (𝒮 c P) (All.++⁺ rs ps)
    → UsefulAcc P (con c rs ∷ ps)

  step-∣ : {P : PatMat (α ∷ αs)} {p q : Pat α} {ps : Pats αs}
    → UsefulAcc P (p ∷ ps)
    → UsefulAcc P (q ∷ ps)
    → UsefulAcc P (p ∣ q ∷ ps)

useful?′ : (P : PatMat αs) (ps : Pats αs) → UsefulAcc P ps → Dec (Useful P ps)
useful?′ P (∙ ∷ qs) (step-∙ h h′) with ∃missingCon? P
... | inj₁ ∃c∉P =
      Dec.map (𝒟-preserves-usefulness⇔ ∃c∉P) (useful?′ (𝒟 P) qs (h ∃c∉P))
... | inj₂ ∀c∈P =
      Dec.map ∃𝒮-preserves-usefulness-∙⇔
        (Fin.any? λ c → useful?′ (𝒮 c P) (All.++⁺ ∙* qs) (h′ c (∀c∈P c)))
useful?′ P (con c rs ∷ ps) (step-con h) =
  Dec.map 𝒮-preserves-usefulness-con⇔
    (useful?′ (𝒮 c P) (All.++⁺ rs ps) h)
useful?′ P (r₁ ∣ r₂ ∷ ps) (step-∣ h h′) =
  Dec.map merge-useful⇔
    (useful?′ P (r₁ ∷ ps) h ⊎-dec useful?′ P (r₂ ∷ ps) h′)
useful?′ [] [] _ = yes useful-[]-[]
useful?′ (_ ∷ _) [] _ = no ¬useful-∷-[]

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

patsSize : Pats αs → ℕ → ℕ
patsSize [] n = n
patsSize (∙ ∷ ps) n = patsSize ps n
patsSize (con _ rs ∷ ps) n = suc (patsSize rs (patsSize ps n))
patsSize (r₁ ∣ r₂ ∷ ps) n = suc (patsSize (r₁ ∷ ps) n + patsSize (r₂ ∷ ps) n)

patMatSize : PatMat αs → ℕ
patMatSize P = List.sum (List.map (flip patsSize 0) P)

patsSize-++ : (ps : Pats αs) (qs : Pats βs) (n : ℕ)
  → patsSize (All.++⁺ ps qs) n ≡ patsSize ps (patsSize qs n)
patsSize-++ [] qs n = refl
patsSize-++ (∙ ∷ ps) qs n = patsSize-++ ps qs n
patsSize-++ (con _ rs ∷ ps) qs n = cong (suc ∘ patsSize rs) (patsSize-++ ps qs n)
patsSize-++ (r₁ ∣ r₂ ∷ ps) qs n = cong suc (cong₂ _+_ (patsSize-++ (r₁ ∷ ps) qs n) (patsSize-++ (r₂ ∷ ps) qs n))

patsSize∙* : ∀ αs n → patsSize (∙* {αs = αs}) n ≡ n
patsSize∙* [] n = refl
patsSize∙* (α ∷ αs) n = patsSize∙* αs n

patMatSize-++ : (P Q : PatMat αs) → patMatSize (P ++ Q) ≡ patMatSize P + patMatSize Q
patMatSize-++ P Q
  rewrite map-++ (flip patsSize 0) P Q
  | sum-++ (List.map (flip patsSize 0) P) (List.map (flip patsSize 0) Q)
  = refl

𝒮-aux-≤ : (c : Con α) (ps : Pats (α ∷ αs)) → patMatSize (𝒮-aux c ps) ≤ patsSize ps 0
𝒮-aux-≤ {α} c (∙ ∷ ps)
  rewrite patsSize-++ (∙* {αs = argsTy α c}) ps 0
  | patsSize∙* (argsTy α c) (patsSize ps 0)
  | ℕ.+-identityʳ (patsSize ps 0)
  = ℕ.≤-refl
𝒮-aux-≤ c (con c′ rs ∷ ps) with c Fin.≟ c′
... | yes refl
        rewrite patsSize-++ rs ps 0
        | ℕ.+-identityʳ (patsSize rs (patsSize ps 0))
        = ℕ.n≤1+n (patsSize rs (patsSize ps 0))
... | no _ = ℕ.<⇒≤ ℕ.0<1+n
𝒮-aux-≤ c (r₁ ∣ r₂ ∷ ps) =
  -- rewrite messed up termination check, so do it manually
  begin
    patMatSize (𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps))
  ≡⟨ patMatSize-++ (𝒮-aux c (r₁ ∷ ps)) (𝒮-aux c (r₂ ∷ ps)) ⟩
    patMatSize (𝒮-aux c (r₁ ∷ ps)) + patMatSize (𝒮-aux c (r₂ ∷ ps))
  ≤⟨ ℕ.+-mono-≤ (𝒮-aux-≤ c (r₁ ∷ ps)) (𝒮-aux-≤ c (r₂ ∷ ps)) ⟩
    patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0
  <⟨ ℕ.n<1+n _ ⟩
    suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
  ∎
  where open ℕ.≤-Reasoning

-- 𝒮 does not increase the pattern matrix size
𝒮-≤ : (c : Con α) (P : PatMat (α ∷ αs)) → patMatSize (𝒮 c P) ≤ patMatSize P
𝒮-≤ c [] = ℕ.≤-refl
𝒮-≤ c (ps ∷ P)
  rewrite patMatSize-++ (𝒮-aux c ps) (𝒮 c P)
  = ℕ.+-mono-≤ (𝒮-aux-≤ c ps) (𝒮-≤ c P)

∈⇒𝒮-aux-< : (c : Con α) (ps : Pats (α ∷ αs))
  → c ∈ All.head ps
  → patMatSize (𝒮-aux c ps) < patsSize ps 0
∈⇒𝒮-aux-< c (con d rs ∷ ps) c≡d with c Fin.≟ d
... | yes refl
      rewrite patsSize-++ rs ps 0
      | ℕ.+-identityʳ (patsSize rs (patsSize ps 0))
      = ℕ.≤-refl
... | no c≢d = contradiction c≡d c≢d
∈⇒𝒮-aux-< c (r₁ ∣ r₂ ∷ ps) (inj₁ c∈r₁) =
  begin
    suc (patMatSize (𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)))
  ≡⟨ cong suc (patMatSize-++ (𝒮-aux c (r₁ ∷ ps)) (𝒮-aux c (r₂ ∷ ps))) ⟩
    suc (patMatSize (𝒮-aux c (r₁ ∷ ps)) + patMatSize (𝒮-aux c (r₂ ∷ ps)))
  <⟨ ℕ.s<s (ℕ.+-mono-<-≤ (∈⇒𝒮-aux-< c (r₁ ∷ ps) c∈r₁) (𝒮-aux-≤ c (r₂ ∷ ps))) ⟩
    suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
  ∎
  where open ℕ.≤-Reasoning
∈⇒𝒮-aux-< c (r₁ ∣ r₂ ∷ ps) (inj₂ c∈r₂) =
  begin
    suc (patMatSize (𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)))
  ≡⟨ cong suc (patMatSize-++ (𝒮-aux c (r₁ ∷ ps)) (𝒮-aux c (r₂ ∷ ps))) ⟩
    suc (patMatSize (𝒮-aux c (r₁ ∷ ps)) + patMatSize (𝒮-aux c (r₂ ∷ ps)))
  <⟨ ℕ.s<s (ℕ.+-mono-≤-< (𝒮-aux-≤ c (r₁ ∷ ps)) (∈⇒𝒮-aux-< c (r₂ ∷ ps) c∈r₂)) ⟩
    suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
  ∎
  where open ℕ.≤-Reasoning

-- 𝒮 strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
∈⇒𝒮-< : (c : Con α) (P : PatMat (α ∷ αs))
  → Any (λ ps → c ∈ All.head ps) P
  → patMatSize (𝒮 c P) < patMatSize P
∈⇒𝒮-< c (ps ∷ P) (here c∈ps)
  rewrite patMatSize-++ (𝒮-aux c ps) (𝒮 c P)
  = ℕ.+-mono-<-≤ (∈⇒𝒮-aux-< c ps c∈ps) (𝒮-≤ c P)
∈⇒𝒮-< c (ps ∷ P) (there c∈P)
  rewrite patMatSize-++ (𝒮-aux c ps) (𝒮 c P)
  = ℕ.+-mono-≤-< (𝒮-aux-≤ c ps) (∈⇒𝒮-< c P c∈P)

𝒟-aux-≤ : (ps : Pats (α ∷ αs)) → patMatSize (𝒟-aux ps) ≤ patsSize ps 0
𝒟-aux-≤ (∙ ∷ ps)
  rewrite ℕ.+-identityʳ (patsSize ps 0)
  = ℕ.≤-refl
𝒟-aux-≤ (con _ _ ∷ ps) = ℕ.<⇒≤ ℕ.0<1+n
𝒟-aux-≤ (r₁ ∣ r₂ ∷ ps) =
  begin
    patMatSize (𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps))
  ≡⟨ patMatSize-++ (𝒟-aux (r₁ ∷ ps)) (𝒟-aux (r₂ ∷ ps)) ⟩
    patMatSize (𝒟-aux (r₁ ∷ ps)) + patMatSize (𝒟-aux (r₂ ∷ ps))
  ≤⟨ ℕ.+-mono-≤ (𝒟-aux-≤ (r₁ ∷ ps)) (𝒟-aux-≤ (r₂ ∷ ps)) ⟩
    patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0
  <⟨ ℕ.n<1+n _ ⟩
    suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
  ∎
  where open ℕ.≤-Reasoning

-- 𝒟 does not increase the pattern matrix size
𝒟-≤ : (P : PatMat (α ∷ αs)) → patMatSize (𝒟 P) ≤ patMatSize P
𝒟-≤ [] = ℕ.≤-refl
𝒟-≤ (ps ∷ P)
  rewrite patMatSize-++ (𝒟-aux ps) (𝒟 P)
  = ℕ.+-mono-≤ (𝒟-aux-≤ ps) (𝒟-≤ P)

SomeProblem : Set
SomeProblem = ∃[ αs ] PatMat αs × Pats αs

problemSize : SomeProblem → ℕ × ℕ
problemSize (αs , P , ps) = (patMatSize P + patsSize ps 0) , List.length αs

-- Lexicographic ordering on SomeProblem
_⊏_ : (P Q : SomeProblem) → Set
_⊏_ = ×-Lex _≡_ _<_ _<_ on problemSize

-- _⊏_ is well-founded
⊏-wellFounded : WellFounded _⊏_
⊏-wellFounded = On.wellFounded problemSize (×-wellFounded ℕ.<-wellFounded ℕ.<-wellFounded)

-- 𝒮 strictly reduces the problem size
𝒮-⊏ : (P : PatMat (α ∷ αs)) (c : Con α) (rs : Pats (argsTy α c)) (ps : Pats αs)
  → (-, 𝒮 c P , All.++⁺ rs ps) ⊏ (-, P , con c rs ∷ ps)
𝒮-⊏ P c rs ps
  rewrite patsSize-++ rs ps 0
  = inj₁ (ℕ.+-mono-≤-< (𝒮-≤ c P) (ℕ.n<1+n _))

-- 𝒟 strictly reduces the problem size
𝒟-⊏ : (P : PatMat (α ∷ αs)) (qs : Pats αs)
  → (-, 𝒟 P , qs) ⊏ (-, P , ∙ ∷ qs)
𝒟-⊏ P qs with ℕ.m≤n⇒m<n∨m≡n (𝒟-≤ P)
... | inj₁ 𝒟P<P = inj₁ (ℕ.+-monoˡ-< (patsSize qs 0) 𝒟P<P)
... | inj₂ 𝒟P≡P = inj₂ (cong (_+ patsSize qs 0) 𝒟P≡P , ℕ.n<1+n _)

-- 𝒮 strictly reduces the problem size if the constructor is in the first column of the matrix
∈⇒𝒮-⊏ : (c : Con α) (P : PatMat (α ∷ αs)) (qs : Pats αs)
  → Any (λ ps → c ∈ All.head ps) P
  → (-, 𝒮 c P , All.++⁺ ∙* qs) ⊏ (-, P , ∙ ∷ qs)
∈⇒𝒮-⊏ {α} c P qs c∈P
  rewrite patsSize-++ (∙* {αs = argsTy α c}) qs 0
  | patsSize∙* (argsTy α c) (patsSize qs 0)
  = inj₁ (ℕ.+-monoˡ-< (patsSize qs 0) (∈⇒𝒮-< c P c∈P))

-- Choosing the left pattern strictly reduces the problem size
∣-⊏ₗ : (P : PatMat (α ∷ αs)) (r₁ r₂ : Pat α) (ps : Pats αs)
  → (_ , P , r₁ ∷ ps) ⊏ (_ , P , r₁ ∣ r₂ ∷ ps)
∣-⊏ₗ P r₁ r₂ ps =
  inj₁ (ℕ.+-monoʳ-< (patMatSize P) (ℕ.m≤m+n (suc (patsSize (r₁ ∷ ps) 0)) (patsSize (r₂ ∷ ps) 0)))

-- Choosing the right pattern strictly reduces the problem size
∣-⊏ᵣ : (P : PatMat (α ∷ αs)) (r₁ r₂ : Pat α) (ps : Pats αs)
  → (_ , P , r₂ ∷ ps) ⊏ (_ , P , r₁ ∣ r₂ ∷ ps)
∣-⊏ᵣ P r₁ r₂ ps =
  inj₁ (ℕ.+-monoʳ-< (patMatSize P) (ℕ.s<s (ℕ.m≤n+m (patsSize (r₂ ∷ ps) 0) (patsSize (r₁ ∷ ps) 0))))

∀UsefulAcc-aux : (P : PatMat αs) (ps : Pats αs)
  → Acc _⊏_ (-, P , ps)
  → UsefulAcc P ps
∀UsefulAcc-aux P [] _ = done
∀UsefulAcc-aux P (∙ ∷ ps) (acc h) =
  step-∙
    (λ _ → ∀UsefulAcc-aux (𝒟 P) ps (h (𝒟-⊏ P ps)))
    (λ c c∈P → ∀UsefulAcc-aux (𝒮 c P) (All.++⁺ ∙* ps) (h (∈⇒𝒮-⊏ c P ps c∈P)))
∀UsefulAcc-aux P (con c rs ∷ ps) (acc h) =
  step-con (∀UsefulAcc-aux (𝒮 c P) (All.++⁺ rs ps) (h (𝒮-⊏ P c rs ps)))
∀UsefulAcc-aux P (r₁ ∣ r₂ ∷ ps) (acc h) =
  step-∣
    (∀UsefulAcc-aux P (r₁ ∷ ps) (h (∣-⊏ₗ P r₁ r₂ ps)))
    (∀UsefulAcc-aux P (r₂ ∷ ps) (h (∣-⊏ᵣ P r₁ r₂ ps)))

∀UsefulAcc : (P : PatMat αs) (ps : Pats αs) → UsefulAcc P ps
∀UsefulAcc P ps = ∀UsefulAcc-aux P ps (⊏-wellFounded _)

--------------------------------------------------------------------------------
-- Entrypoint

useful? : (P : PatMat αs) (ps : Pats αs) → Dec (Useful P ps)
useful? P ps = useful?′ P ps (∀UsefulAcc P ps)

exhaustive? : (P : PatMat αs) → Exhaustive P ⊎ NonExhaustive P
exhaustive? P with useful? P ∙*
... | true because [h] = inj₂ (NonExhaustive′→NonExhaustive (invert [h]))
... | false because [h] = inj₁ (Exhaustive′→Exhaustive (invert [h]))
