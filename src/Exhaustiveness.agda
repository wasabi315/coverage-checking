module Exhaustiveness where

open import Data.Bool using (true; false; _∧_)
open import Data.Fin as Fin using (zero; suc)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ⊥; ⁅_⁆; _∪_; ∁; ⋃; Nonempty; Empty)
open import Data.Fin.Subset.Properties using (x∈∁p⇒x∉p; x∉p⇒x∈∁p; ∉⊥; x∈⁅x⁆; x∈⁅y⁆⇔x≡y; nonempty?)
open import Data.Fin.Properties using (any?)
open import Data.List as List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties as Any using (¬Any[])
open import Data.List.Relation.Unary.First as First using (First; toAny)
open import Data.List.Relation.Unary.First.Properties as First using (All⇒¬First)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (id; _∘_; _⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; ≢-sym)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _⊎-dec_; _×-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)

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
  ... | yes P≼vs = P≼vs
  ... | no P⋠vs = contradiction (vs , ¬First⇒¬Any id P⋠vs , ∙*≼ ) exh

  -- The two definitions of exhaustiveness are equivalent
  Exhaustive′⇔Exhaustive : Exhaustive′ P ⇔ Exhaustive P
  Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

--------------------------------------------------------------------------------
-- Operations on patterns used in the algorithm

-- Set of root constructors of a pattern
rootCons : Pat α → ConSet α
rootCons ∙ = ⊥
rootCons (con c _) = ⁅ c ⁆
rootCons (p ∣ q) = rootCons p ∪ rootCons q

emptyRootCons? : (p : Pat α) → Dec (Empty (rootCons p))
emptyRootCons? ∙ = yes (∉⊥ ∘ proj₂)
emptyRootCons? (con c _) = no λ empty⁅c⁆ → empty⁅c⁆ (c , x∈⁅x⁆ c)
emptyRootCons? (p ∣ q) = Dec.map Empty∪⇔ (emptyRootCons? p ×-dec emptyRootCons? q)

-- Set of root constructors in the first column of a pattern matrix
presentCons : PatMat (α ∷ αs) → ConSet α
presentCons = ⋃ ∘ List.map (rootCons ∘ All.head)

emptyPresentCons? : (P : PatMat (α ∷ αs)) → Dec (Empty (presentCons P))
emptyPresentCons? [] = yes (∉⊥ ∘ proj₂)
emptyPresentCons? (ps ∷ P) = Dec.map Empty∪⇔ (emptyRootCons? (All.head ps) ×-dec emptyPresentCons? P)

∃missingCon? : (P : PatMat (α ∷ αs)) → Dec (∃[ c ] c ∉ presentCons P)
∃missingCon? {α = α} P with emptyPresentCons? P
... | yes empty = yes (inhabCon α , empty ∘ (inhabCon α ,_))
... | no _ =
      Dec.map′
        (Product.map₂ x∈∁p⇒x∉p)
        (Product.map₂ x∉p⇒x∈∁p)
        (nonempty? (∁ (presentCons P)))
{-
-- The above definition has better decidability than the following one;
-- When α is abstract, you can't decide how many constructors there are in α, therefore you can't decide if there is a missing constructor.
-- The definition above exploits the fact that you can decide if the set is empty without knowing the number of constructors.

∃missingCon? =
  Dec.map′ (Product.map₂ x∈∁p⇒x∉p) (Product.map₂ x∉p⇒x∈∁p) (nonempty? (∁ (presentCons P)))
-}

-- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.
𝒮-aux : (c : Con α) → Pats (α ∷ αs) → PatMat (argsTy α c ++ αs)
𝒮-aux c (∙ ∷ ps) = (∙* ++ₚ ps) ∷ []
𝒮-aux c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = (rs ++ₚ ps) ∷ []
𝒮-aux c (r₁ ∣ r₂ ∷ ps) = 𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)

𝒮 : (c : Con α) → PatMat (α ∷ αs) → PatMat (argsTy α c ++ αs)
𝒮 = concatMap ∘ 𝒮-aux

-- Default matrix: filters out clauses whose first pattern is a constructor pattern
𝒟-aux : Pats (α ∷ αs) → PatMat αs
𝒟-aux (∙ ∷ ps) = ps ∷ []
𝒟-aux (con _ _ ∷ ps) = []
𝒟-aux (r₁ ∣ r₂ ∷ ps) = 𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps)

𝒟 : PatMat (α ∷ αs) → PatMat αs
𝒟 = concatMap 𝒟-aux

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

  -- "Unspecializing" preserves ≼
  𝒮-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
    → 𝒮 c P ≼** (us ++ᵥ vs)
    → P ≼** con {α} c us ∷ vs
  𝒮-preserves-≼⁻ = Any.map 𝒮-aux-preserves-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

  𝒮-preserves-≼⇔ : {P : PatMat (α ∷ αs)}
    → P ≼** con {α} c us ∷ vs ⇔ 𝒮 c P ≼** (us ++ᵥ vs)
  𝒮-preserves-≼⇔ = mk⇔ 𝒮-preserves-≼ 𝒮-preserves-≼⁻


module _ {c : Con α} {us : Vals (argsTy α c)} {vs : Vals αs} where

  𝒟-aux-preserves-≼ : {ps : Pats (α ∷ αs)}
    → c ∉ rootCons (All.head ps)
    → ps ≼* con {α} c us ∷ vs
    → 𝒟-aux ps ≼** vs
  𝒟-aux-preserves-≼ {∙ ∷ ps} _ ∙ps≼cusvs = here (∷⁻ ∙ps≼cusvs .proj₂)
  𝒟-aux-preserves-≼ {con d rs ∷ ps} c∉⁅d⁆ drsps≼cusvs =
    contradiction (Equivalence.from x∈⁅y⁆⇔x≡y (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁)))) c∉⁅d⁆
  𝒟-aux-preserves-≼ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map
      (𝒟-aux-preserves-≼ (x∉p∪q⁻ˡ c∉r₁∪r₂))
      (𝒟-aux-preserves-≼ (x∉p∪q⁻ʳ c∉r₁∪r₂)) ∘
    ∣≼*⁻

  -- If c is not in presentCons P, 𝒟 preserves ≼
  𝒟-preserves-≼ : {P : PatMat (α ∷ αs)}
    → c ∉ presentCons P
    → P ≼** con {α} c us ∷ vs
    → 𝒟 P ≼** vs
  𝒟-preserves-≼ {ps ∷ P} c∉ps∪P (here ps≼cusvs) =
    Any.++⁺ˡ (𝒟-aux-preserves-≼ (x∉p∪q⁻ˡ c∉ps∪P) ps≼cusvs)
  𝒟-preserves-≼ {ps ∷ P} c∉ps∪P (there P≼cusvs) =
    Any.++⁺ʳ _ (𝒟-preserves-≼ (x∉p∪q⁻ʳ c∉ps∪P) P≼cusvs)


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
useful-[]-[] = [] , ¬Any[] , []

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

  -- If presentCons P is not complete, and ps is useful wrt 𝒟 P, ∙ ∷ ps is also useful wrt P.
  -- That means, it suffices to check for usefulness of ps wrt 𝒟 P if presentCons P is not complete.
  𝒟-preserves-usefulness⁻ :
      ∃[ c ] c ∉ presentCons P
    → Useful (𝒟 P) ps
    → Useful P (∙ ∷ ps)
  𝒟-preserves-usefulness⁻ (c , c∉P) (vs , 𝒟P⋠vs , ps≼vs) =
    inhabOf c ∷ vs , contraposition (𝒟-preserves-≼ c∉P) 𝒟P⋠vs , ∙≼ ∷ ps≼vs

  𝒟-preserves-usefulness⇔ :
      ∃[ c ] c ∉ presentCons P
    → Useful (𝒟 P) ps ⇔ Useful P (∙ ∷ ps)
  𝒟-preserves-usefulness⇔ ∃c∉P =
    mk⇔ (𝒟-preserves-usefulness⁻ ∃c∉P) 𝒟-preserves-usefulness

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

{-# TERMINATING #-}
useful? : (P : PatMat αs) (ps : Pats αs) → Dec (Useful P ps)
useful? [] [] = yes useful-[]-[]
useful? (_ ∷ _) [] = no ¬useful-∷-[]
useful? P (∙ ∷ ps) with ∃missingCon? P
... | yes ∃c∉P =
      Dec.map (𝒟-preserves-usefulness⇔ ∃c∉P) (useful? (𝒟 P) ps)
... | no _ =
      Dec.map ∃𝒮-preserves-usefulness-∙⇔ (any? λ c → useful? (𝒮 c P) (All.++⁺ ∙* ps))
useful? P (con c rs ∷ ps) =
  Dec.map 𝒮-preserves-usefulness-con⇔ (useful? (𝒮 c P) (All.++⁺ rs ps))
useful? P (r₁ ∣ r₂ ∷ ps) =
  Dec.map merge-useful⇔ (useful? P (r₁ ∷ ps) ⊎-dec useful? P (r₂ ∷ ps))

exhaustive? : (P : PatMat αs) → Exhaustive P ⊎ NonExhaustive P
exhaustive? P with useful? P ∙*
... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
... | no h = inj₁ (Exhaustive′→Exhaustive h)
