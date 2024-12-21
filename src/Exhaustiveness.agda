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
specialize : (c : Con α) → PatMat (α ∷ αs) → PatMat (args α c ++ αs)
specializeBody : (c : Con α) → Pats (α ∷ αs) → PatMat (args α c ++ αs)

specialize = concatMap ∘ specializeBody
specializeBody c (∙ ∷ ps) = All.++⁺ ∙* ps ∷ []
specializeBody c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = All.++⁺ rs ps ∷ []
specializeBody c (r₁ ∣ r₂ ∷ ps) = specializeBody c (r₁ ∷ ps) ++ specializeBody c (r₂ ∷ ps)

-- Default matrix: filters out clauses whose first pattern is a constructor pattern
default : PatMat (α ∷ αs) → PatMat αs
defaultBody : Pats (α ∷ αs) → PatMat αs

default = concatMap defaultBody
defaultBody (∙ ∷ ps) = ps ∷ []
defaultBody (con _ _ ∷ ps) = []
defaultBody (r₁ ∣ r₂ ∷ ps) = defaultBody (r₁ ∷ ps) ++ defaultBody (r₂ ∷ ps)

--------------------------------------------------------------------------------
-- Properties of ≼ and specialize/default

module _ {c : Con α} {us : Vals (args α c)} {vs : Vals αs} where

  specializeBody-preserves-≼ : {ps : Pats (α ∷ αs)}
    → ps ≼* con {α} c us ∷ vs
    → specializeBody c ps ≼** All.++⁺ us vs
  specializeBody-preserves-≼ {∙ ∷ ps} ∙ps≼cusvs = here (∙≼*⁻ ∙ps≼cusvs)
  specializeBody-preserves-≼ {con d rs ∷ ps} drsps≼cusvs with c Fin.≟ d
  ... | no c≢d = contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c≢d
  ... | yes refl = here (con≼*⁻ drsps≼cusvs)
  specializeBody-preserves-≼ {r₁ ∣ r₂ ∷ ps} =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map specializeBody-preserves-≼ specializeBody-preserves-≼ ∘
    ∣≼*⁻

  -- specialize preserves ≼
  specialize-preserves-≼ : {P : PatMat (α ∷ αs)}
    → P ≼** con {α} c us ∷ vs
    → specialize c P ≼** All.++⁺ us vs
  specialize-preserves-≼ = Any.concat⁺ ∘ Any.gmap specializeBody-preserves-≼

  specializeBody-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
    → specializeBody c ps ≼** All.++⁺ us vs
    → ps ≼* con {α} c us ∷ vs
  specializeBody-preserves-≼⁻ {∙ ∷ ps} (here ∙*ps≼usvs) = ∙≼*⁺ ∙*ps≼usvs
  specializeBody-preserves-≼⁻ {con d rs ∷ ps} _ with c Fin.≟ d
  specializeBody-preserves-≼⁻ {con d rs ∷ ps} (here drsps≼cusvs) | yes refl = con≼*⁺ drsps≼cusvs
  specializeBody-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map specializeBody-preserves-≼⁻ specializeBody-preserves-≼⁻ ∘ Any.++⁻ _

  -- "Unspecializing" preserves ≼
  specialize-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
    → specialize c P ≼** All.++⁺ us vs
    → P ≼** con {α} c us ∷ vs
  specialize-preserves-≼⁻ = Any.map specializeBody-preserves-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

  specialize-preserves-≼⇔ : {P : PatMat (α ∷ αs)}
    → P ≼** con {α} c us ∷ vs ⇔ specialize c P ≼** All.++⁺ us vs
  specialize-preserves-≼⇔ = mk⇔ specialize-preserves-≼ specialize-preserves-≼⁻


module _ {c : Con α} {us : Vals (args α c)} {vs : Vals αs} where

  defaultBody-preserves-≼ : {ps : Pats (α ∷ αs)}
    → c ∉ rootCons (All.head ps)
    → ps ≼* con {α} c us ∷ vs
    → defaultBody ps ≼** vs
  defaultBody-preserves-≼ {∙ ∷ ps} _ ∙ps≼cusvs = here (∷⁻ ∙ps≼cusvs .proj₂)
  defaultBody-preserves-≼ {con d rs ∷ ps} c∉⁅d⁆ drsps≼cusvs =
    contradiction (Equivalence.from x∈⁅y⁆⇔x≡y (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁)))) c∉⁅d⁆
  defaultBody-preserves-≼ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ =
    [ Any.++⁺ˡ , Any.++⁺ʳ _ ] ∘
    Sum.map
      (defaultBody-preserves-≼ (x∉p∪q⁻ˡ c∉r₁∪r₂))
      (defaultBody-preserves-≼ (x∉p∪q⁻ʳ c∉r₁∪r₂)) ∘
    ∣≼*⁻

  -- If c is not in presentCons P, default preserves ≼
  default-preserves-≼ : {P : PatMat (α ∷ αs)}
    → c ∉ presentCons P
    → P ≼** con {α} c us ∷ vs
    → default P ≼** vs
  default-preserves-≼ {ps ∷ P} c∉ps∪P (here ps≼cusvs) =
    Any.++⁺ˡ (defaultBody-preserves-≼ (x∉p∪q⁻ˡ c∉ps∪P) ps≼cusvs)
  default-preserves-≼ {ps ∷ P} c∉ps∪P (there P≼cusvs) =
    Any.++⁺ʳ _ (default-preserves-≼ (x∉p∪q⁻ʳ c∉ps∪P) P≼cusvs)


module _ {v : Val α} {vs : Vals αs} where

  defaultBody-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
    → defaultBody ps ≼** vs
    → ps ≼* v ∷ vs
  defaultBody-preserves-≼⁻ {∙ ∷ ps} (here ∙ps≼vvs) = ∙≼ ∷ ∙ps≼vvs
  defaultBody-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
    ∣≼*⁺ ∘ Sum.map defaultBody-preserves-≼⁻ defaultBody-preserves-≼⁻ ∘ Any.++⁻ _

  default-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
    → default P ≼** vs
    → P ≼** v ∷ vs
  default-preserves-≼⁻ = Any.map defaultBody-preserves-≼⁻ ∘ Any.map⁻ ∘ Any.concat⁻ _

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


module _ {P : PatMat (α ∷ αs)} {c : Con α} {rs : Pats (args α c)} {ps : Pats αs} where

  specialize-preserves-usefulness-con :
      Useful P (con c rs ∷ ps)
    → Useful (specialize c P) (All.++⁺ rs ps)
  specialize-preserves-usefulness-con (con c vs ∷ us , P⋠cvsus , con≼ rs≼vs ∷ ps≼us) =
    All.++⁺ vs us , contraposition specialize-preserves-≼⁻ P⋠cvsus , ++⁺ rs≼vs ps≼us

  specialize-preserves-usefulness-con⁻ :
      Useful (specialize c P) (All.++⁺ rs ps)
    → Useful P (con c rs ∷ ps)
  specialize-preserves-usefulness-con⁻ (usvs , specializeP⋠usvs , rsps≼usvs)
    with us , vs , refl , rs≼us , ps≼vs ← split rs rsps≼usvs =
    con c us ∷ vs , contraposition specialize-preserves-≼ specializeP⋠usvs , con≼ rs≼us ∷ ps≼vs

  -- con c rs ∷ ps is useful wrt P iff rs ++ ps is useful wrt specialize c P
  specialize-preserves-usefulness-con⇔ :
      Useful (specialize c P) (All.++⁺ rs ps)
    ⇔ Useful P (con c rs ∷ ps)
  specialize-preserves-usefulness-con⇔ =
    mk⇔ specialize-preserves-usefulness-con⁻ specialize-preserves-usefulness-con


module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`
  ∃specialize-preserves-usefulness-∙ :
      Useful P (∙ ∷ ps)
    → ∃[ c ] Useful (specialize c P) (All.++⁺ ∙* ps)
  ∃specialize-preserves-usefulness-∙ (con c us ∷ vs , P⋠cusvs , ∙≼ ∷ ps≼vs) =
    c , All.++⁺ us vs , contraposition specialize-preserves-≼⁻ P⋠cusvs , ++⁺ ∙*≼ ps≼vs

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`, `∙ ∷ ps` is also useful wrt P
  ∃specialize-preserves-usefulness-∙⁻ :
      ∃[ c ] Useful (specialize c P) (All.++⁺ ∙* ps)
    → Useful P (∙ ∷ ps)
  ∃specialize-preserves-usefulness-∙⁻ (c , usvs , specializeP⋠usvs , ∙*ps≼usvs)
    with us , vs , refl , _ , ps≼vs ← split {args α c} ∙* ∙*ps≼usvs =
    con c us ∷ vs , contraposition specialize-preserves-≼ specializeP⋠usvs , ∙≼ ∷ ps≼vs

  -- ∙ ∷ ps is useful wrt P iff ∙* ++ ps is useful wrt specialize c P
  ∃specialize-preserves-usefulness-∙⇔ :
      (∃[ c ] Useful (specialize c P) (All.++⁺ ∙* ps))
    ⇔ Useful P (∙ ∷ ps)
  ∃specialize-preserves-usefulness-∙⇔ =
    mk⇔ ∃specialize-preserves-usefulness-∙⁻ ∃specialize-preserves-usefulness-∙


module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

  -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
  default-preserves-usefulness : Useful P (∙ ∷ ps) → Useful (default P) ps
  default-preserves-usefulness (v ∷ vs  , P⋠vvs , ∙≼ ∷ ps≼vs) =
    vs , contraposition default-preserves-≼⁻ P⋠vvs , ps≼vs

  -- If presentCons P is not complete, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
  -- That means, it suffices to check for usefulness of ps wrt default P if presentCons P is not complete.
  default-preserves-usefulness⁻ :
      ∃[ c ] c ∉ presentCons P
    → Useful (default P) ps
    → Useful P (∙ ∷ ps)
  default-preserves-usefulness⁻ (c , c∉P) (vs , defaultP⋠vs , ps≼vs) =
    inhabOf c ∷ vs , contraposition (default-preserves-≼ c∉P) defaultP⋠vs , ∙≼ ∷ ps≼vs

  default-preserves-usefulness⇔ :
      ∃[ c ] c ∉ presentCons P
    → Useful (default P) ps ⇔ Useful P (∙ ∷ ps)
  default-preserves-usefulness⇔ ∃c∉P =
    mk⇔ (default-preserves-usefulness⁻ ∃c∉P) default-preserves-usefulness

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

{-# TERMINATING #-}
useful? : (P : PatMat αs) (ps : Pats αs) → Dec (Useful P ps)
useful? [] [] = yes useful-[]-[]
useful? (_ ∷ _) [] = no ¬useful-∷-[]
useful? P (∙ ∷ ps) with ∃missingCon? P
... | yes ∃c∉P =
      Dec.map (default-preserves-usefulness⇔ ∃c∉P)
        (useful? (default P) ps)
... | no _ =
      Dec.map ∃specialize-preserves-usefulness-∙⇔
        (any? λ c → useful? (specialize c P) (All.++⁺ ∙* ps))
useful? P (con c rs ∷ ps) =
  Dec.map specialize-preserves-usefulness-con⇔
    (useful? (specialize c P) (All.++⁺ rs ps))
useful? P (r₁ ∣ r₂ ∷ ps) =
  Dec.map merge-useful⇔
    (useful? P (r₁ ∷ ps) ⊎-dec useful? P (r₂ ∷ ps))

exhaustive? : (P : PatMat αs) → Exhaustive P ⊎ NonExhaustive P
exhaustive? P with useful? P ∙*
... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
... | no h = inj₁ (Exhaustive′→Exhaustive h)
