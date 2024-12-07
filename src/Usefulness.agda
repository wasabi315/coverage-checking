module Usefulness where

open import Data.Fin as Fin using (zero; suc)
open import Data.Fin.Subset using (Subset; _∉_; ⊥; ⁅_⁆; _∪_; ∁; ⋃; Nonempty)
open import Data.Fin.Subset.Properties using (x∉⁅y⁆⇒x≢y; x∈∁p⇒x∉p; nonempty?)
open import Data.Fin.Properties using (any?)
open import Data.List as List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.First as First using (First)
open import Data.List.Relation.Unary.First.Properties as First using (All⇒¬First)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; ≢-sym)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no; _⊎-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction; contraposition)

open import Extra
open import Pattern

private
  variable
    α β : Ty
    αs βs : List Ty

--------------------------------------------------------------------------------
-- Exhaustiveness and usefulness

-- There is a matching row in pss for every list of values
Exhaustive : PatMat αs → Set
Exhaustive pss = ∀ vs → Match vs pss

-- There is a list of values that does not match any row in pss
NonExhaustive : PatMat αs → Set
NonExhaustive pss = ∃[ vs ] ¬ Match vs pss

-- ps is useful with respect to pss if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in pss
-- Usefulness can also be used to formulate redundancy
Useful : Pats αs → PatMat αs → Set
Useful ps pss = ∃[ vs ] ps ≼* vs × All (_⋠* vs) pss

-- non-exhaustiveness defined in terms of usefulness:
-- pss is non-exhaustive if ∙* is useful with respect to pss
NonExhaustive′ : PatMat αs → Set
NonExhaustive′ = Useful ∙*

-- pss is exhaustive if ∙* is not useful with respect to pss
Exhaustive′ : PatMat αs → Set
Exhaustive′ pss = ¬ NonExhaustive′ pss

module _ {pss : PatMat αs} where

  NonExhaustive′→NonExhaustive : NonExhaustive′ pss → NonExhaustive pss
  NonExhaustive′→NonExhaustive (vs , _ , ∙*ps⋠vs) = vs , All⇒¬First id ∙*ps⋠vs

  NonExhaustive→NonExhaustive′ : NonExhaustive pss → NonExhaustive′ pss
  NonExhaustive→NonExhaustive′ (vs , pss⋠vs) = vs , ∙*≼ , ¬First⇒All id pss⋠vs

  -- The two definitions of non-exhaustiveness are equivalent
  NonExhaustive′⇔NonExhaustive : NonExhaustive′ pss ⇔ NonExhaustive pss
  NonExhaustive′⇔NonExhaustive = mk⇔ NonExhaustive′→NonExhaustive NonExhaustive→NonExhaustive′

  Exhaustive→Exhaustive′ : Exhaustive pss → Exhaustive′ pss
  Exhaustive→Exhaustive′ exh (vs , _ , pss⋠vs) = All⇒¬First id pss⋠vs (exh vs)

  Exhaustive′→Exhaustive : Exhaustive′ pss → Exhaustive pss
  Exhaustive′→Exhaustive exh vs with match? vs pss
  ... | yes pss≼vs = pss≼vs
  ... | no pss⋠vs = contradiction (vs , ∙*≼ , ¬First⇒All id pss⋠vs) exh

  -- The two definitions of exhaustiveness are equivalent
  Exhaustive′⇔Exhaustive : Exhaustive′ pss ⇔ Exhaustive pss
  Exhaustive′⇔Exhaustive = mk⇔ Exhaustive′→Exhaustive Exhaustive→Exhaustive′

--------------------------------------------------------------------------------

-- Set of root constructors of a pattern
rootCons : Pat α → ConSet α
rootCons ∙ = ⊥
rootCons (con c _) = ⁅ c ⁆
rootCons (p ∣ q) = rootCons p ∪ rootCons q

-- Set of root constructors in the first column of a pattern matrix
Σ : PatMat (α ∷ αs) → ConSet α
Σ = ⋃ ∘ List.map (rootCons ∘ All.head)

-- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.
𝒮-aux : ∀ c → Pats (α ∷ αs) → List (Pats (args α c ++ αs))
𝒮-aux c (∙ ∷ ps) = All.++⁺ ∙* ps ∷ []
𝒮-aux c (con d rs ∷ ps) with c Fin.≟ d
... | no _ = []
... | yes refl = All.++⁺ rs ps ∷ []
𝒮-aux c (r₁ ∣ r₂ ∷ ps) = 𝒮-aux c (r₁ ∷ ps) ++ 𝒮-aux c (r₂ ∷ ps)

𝒮 : ∀ c → PatMat (α ∷ αs) → PatMat (args α c ++ αs)
𝒮 = concatMap ∘ 𝒮-aux

-- Default matrix: filters out clauses whose first pattern is a constructor pattern
𝒟-aux : Pats (α ∷ αs) → List (Pats αs)
𝒟-aux (∙ ∷ ps) = ps ∷ []
𝒟-aux (con _ _ ∷ ps) = []
𝒟-aux (r₁ ∣ r₂ ∷ ps) = 𝒟-aux (r₁ ∷ ps) ++ 𝒟-aux (r₂ ∷ ps)

𝒟 : PatMat (α ∷ αs) → PatMat αs
𝒟 = concatMap 𝒟-aux

--------------------------------------------------------------------------------

-- [] is useful wrt []
useful-[]-[] : Useful [] []
useful-[]-[] = [] , [] , []

-- [] is not wrt any non-empty matrix
¬useful-[]-∷ : ∀ {ps pss} → ¬ Useful [] (ps ∷ pss)
¬useful-[]-∷ {ps = []} ([] , _ , ¬[] ∷ _) = ¬[] []

module _ {r₁ r₂ : Pat α} {ps : Pats αs} {pss} where

  useful-∣⁺ : Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss → Useful (r₁ ∣ r₂ ∷ ps) pss
  useful-∣⁺ (inj₁ (vvs , r₁≼v ∷ ps≼vs , pss⋠vvs)) =
    vvs , ∣≼ˡ r₁≼v ∷ ps≼vs , pss⋠vvs
  useful-∣⁺ (inj₂ (vvs , r₂≼v ∷ ps≼vs , pss⋠vvs)) =
    vvs , ∣≼ʳ r₂≼v ∷ ps≼vs , pss⋠vvs

  useful-∣⁻ : Useful (r₁ ∣ r₂ ∷ ps) pss → Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss
  useful-∣⁻ (vvs , ∣≼ˡ r₁≼v ∷ ps≼vs , pss⋠vvs) =
    inj₁ (vvs , r₁≼v ∷ ps≼vs , pss⋠vvs)
  useful-∣⁻ (vvs , ∣≼ʳ r₂≼v ∷ ps≼vs , pss⋠vvs) =
    inj₂ (vvs , r₂≼v ∷ ps≼vs , pss⋠vvs)

  -- (r₁ ∣ r₂ ∷ ps) is useful wrt pss iff (r₁ ∷ ps) or (r₂ ∷ ps) is useful wrt pss
  useful-∣⇔ : (Useful (r₁ ∷ ps) pss ⊎ Useful (r₂ ∷ ps) pss) ⇔ Useful (r₁ ∣ r₂ ∷ ps) pss
  useful-∣⇔ = mk⇔ useful-∣⁺ useful-∣⁻


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  𝒮-aux-pres-⋠ : ∀ {ps}
    → ps ⋠* con {α} c us ∷ vs
    → All (_⋠* All.++⁺ us vs) (𝒮-aux c ps)
  𝒮-aux-pres-⋠ {∙ ∷ ps} ∙ps⋠cusvs = contraposition ∙≼*⁺ ∙ps⋠cusvs ∷ []
  𝒮-aux-pres-⋠ {con d rs ∷ ps} drsps⋠cusvs with c Fin.≟ d
  ... | no _ = []
  ... | yes refl = contraposition con≼*⁺ drsps⋠cusvs ∷ []
  𝒮-aux-pres-⋠ {r₁ ∣ r₂ ∷ ps} r₁₂ps⋠cusvs =
    All.++⁺
      (𝒮-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₁) r₁₂ps⋠cusvs))
      (𝒮-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₂) r₁₂ps⋠cusvs))

  -- 𝒮 preserves ⋠: if all rows in `pss` do not match `con c us ∷ vs`, all rows in the specialized matrix do not match `𝒮 c (con c us ∷ vs) = us ++ vs`.
  𝒮-pres-⋠ : ∀ {pss}
    → All (_⋠* con c us ∷ vs) pss
    → All (_⋠* All.++⁺ us vs) (𝒮 c pss)
  𝒮-pres-⋠ = All.concat⁺ ∘ All.gmap⁺ 𝒮-aux-pres-⋠

  𝒮-aux-pres-⋠⁻ : ∀ {ps}
    → All (_⋠* All.++⁺ us vs) (𝒮-aux c ps)
    → ps ⋠* con {α} c us ∷ vs
  𝒮-aux-pres-⋠⁻ {∙ ∷ ps} (∙*ps⋠usvs ∷ []) (∙≼ ∷ ps≼vs) =
    ∙*ps⋠usvs (++⁺ ∙*≼ ps≼vs)
  𝒮-aux-pres-⋠⁻ {con c rs ∷ ps} 𝒮rsps⋠usvs (con≼ rs≼us ∷ ps≼vs) with c Fin.≟ c | ≟-refl c
  𝒮-aux-pres-⋠⁻ {con c rs ∷ ps} (rsps⋠usvs ∷ []) (con≼ rs≼us ∷ ps≼vs) | _ | refl =
    rsps⋠usvs (++⁺ rs≼us ps≼vs)
  𝒮-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} 𝒮r₁ps𝒮r₂ps⋠usvs (∣≼ˡ r₁≼cus ∷ ps≼vs) =
    𝒮-aux-pres-⋠⁻ (All.++⁻ˡ _ 𝒮r₁ps𝒮r₂ps⋠usvs) (r₁≼cus ∷ ps≼vs)
  𝒮-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} 𝒮r₁ps𝒮r₂ps⋠usvs (∣≼ʳ r₂≼cus ∷ ps≼vs) =
    𝒮-aux-pres-⋠⁻ (All.++⁻ʳ _ 𝒮r₁ps𝒮r₂ps⋠usvs) (r₂≼cus ∷ ps≼vs)

  -- The inverse of 𝒮-pres-⋠: if all rows in the specialized matrix do not match `us ++ vs`, all rows the "unspecialized" matrix do not match `con c us ∷ vs` (unspecialized values).
  𝒮-pres-⋠⁻ : ∀ {pss}
    → All (_⋠* All.++⁺ us vs) (𝒮 c pss)
    → All (_⋠* con c us ∷ vs) pss
  𝒮-pres-⋠⁻ = All.gmap⁻ 𝒮-aux-pres-⋠⁻ ∘ All.concat⁻

  -- Specialization and unspecialization preserve ⋠
  𝒮-pres-⋠⇔ : ∀ {pss}
    → All (_⋠* All.++⁺ us vs) (𝒮 c pss) ⇔ All (_⋠* con c us ∷ vs) pss
  𝒮-pres-⋠⇔ = mk⇔ 𝒮-pres-⋠⁻ 𝒮-pres-⋠


module _ {c} {rs : Pats (args α c)} {ps : Pats αs} {pss : PatMat (α ∷ αs)} where

  useful-con⁺ : Useful (All.++⁺ rs ps) (𝒮 c pss) → Useful (con c rs ∷ ps) pss
  useful-con⁺ (usvs , rsps≼usvs , 𝒮pss⋠usvs)
    with us , vs , refl , rs≼us , ps≼vs ← split rs rsps≼usvs =
    con c us ∷ vs , con≼ rs≼us ∷ ps≼vs , 𝒮-pres-⋠⁻ 𝒮pss⋠usvs

  useful-con⁻ : Useful (con c rs ∷ ps) pss → Useful (All.++⁺ rs ps) (𝒮 c pss)
  useful-con⁻ (con c vs ∷ us , con≼ rs≼vs ∷ ps≼us , pss⋠cvsus) =
    All.++⁺ vs us , ++⁺ rs≼vs ps≼us , 𝒮-pres-⋠ pss⋠cvsus

  -- con c rs ∷ ps is useful wrt pss iff rs ++ ps is useful wrt 𝒮 c pss
  useful-con⇔ : Useful (All.++⁺ rs ps) (𝒮 c pss) ⇔ Useful (con c rs ∷ ps) pss
  useful-con⇔ = mk⇔ useful-con⁺ useful-con⁻


module _ {α αs} {ps : Pats αs} {pss} where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c pss`, `∙ ∷ ps` is also useful wrt pss
  useful-∙-𝒮⁺ : ∃[ c ] Useful (All.++⁺ ∙* ps) (𝒮 c pss) → Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒮⁺ (c , usvs , ∙*ps≼usvs , 𝒮pss⋠usvs)
    with us , vs , refl , _ , ps≼vs ← split {args α c} ∙* ∙*ps≼usvs =
    con c us ∷ vs , ∙≼ ∷ ps≼vs , 𝒮-pres-⋠⁻ 𝒮pss⋠usvs

  -- If `∙ ∷ ps` is useful wrt pss, there exists a constructor c such that `∙* ++ ps` is useful wrt `𝒮 c pss`
  useful-∙-𝒮⁻ : Useful (∙ {α} ∷ ps) pss → ∃[ c ] Useful (All.++⁺ ∙* ps) (𝒮 c pss)
  useful-∙-𝒮⁻ (con c us ∷ vs , ∙≼ ∷ ps≼vs , pss⋠cusvs) =
    c , All.++⁺ us vs , ++⁺ ∙*≼ ps≼vs , 𝒮-pres-⋠ pss⋠cusvs

  -- ∙ ∷ ps is useful wrt pss iff ∙* ++ ps is useful wrt 𝒮 c pss
  useful-∙-𝒮⇔ : (∃[ c ] Useful (All.++⁺ ∙* ps) (𝒮 c pss)) ⇔ Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒮⇔ = mk⇔ useful-∙-𝒮⁺ useful-∙-𝒮⁻

module _ {v : Val α} {vs : Vals αs} where

  𝒟-aux-pres-⋠ : ∀ {ps} → ps ⋠* v ∷ vs → All (_⋠* vs) (𝒟-aux ps)
  𝒟-aux-pres-⋠ {∙ ∷ ps} ∙ps⋠vvs =
    contraposition (∙≼ ∷_) ∙ps⋠vvs ∷ []
  𝒟-aux-pres-⋠ {con _ _ ∷ ps} _ = []
  𝒟-aux-pres-⋠ {r₁ ∣ r₂ ∷ ps} r₁₂ps⋠vvs =
    All.++⁺
      (𝒟-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₁) r₁₂ps⋠vvs))
      (𝒟-aux-pres-⋠ (contraposition (∣≼*⁺ ∘ inj₂) r₁₂ps⋠vvs))

  -- 𝒟 preserves ⋠: if all rows in `pss` do not match `v ∷ vs`, all rows in the default matrix do not match `vs`
  𝒟-pres-⋠ : ∀ {pss} → All (_⋠* v ∷ vs) pss → All (_⋠* vs) (𝒟 pss)
  𝒟-pres-⋠ = All.concat⁺ ∘ All.gmap⁺ 𝒟-aux-pres-⋠


module _ {c} {us : Vals (args α c)} {vs : Vals αs} where

  c∉ps→𝒟-aux-pres-⋠⁻ : ∀ {ps}
    → c ∉ rootCons (All.head ps)
    → All (_⋠* vs) (𝒟-aux ps)
    → ps ⋠* con {α} c us ∷ vs
  c∉ps→𝒟-aux-pres-⋠⁻ {∙ ∷ ps} c∉ps (ps⋠vs ∷ []) (∙≼ ∷ ps≼vs) = ps⋠vs ps≼vs
  c∉ps→𝒟-aux-pres-⋠⁻ {con d _ ∷ ps} c∉⁅d⁆ [] (d≼c ∷ ps≼vs) =
    c≢d→c⋠d (≢-sym (x∉⁅y⁆⇒x≢y c∉⁅d⁆)) d≼c
  c∉ps→𝒟-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ 𝒟r₁ps𝒟r₂ps⋠vs (∣≼ˡ r₁≼cus ∷ ps≼vs) =
    c∉ps→𝒟-aux-pres-⋠⁻ (x∉p∪q⁻ˡ c∉r₁∪r₂) (All.++⁻ˡ _  𝒟r₁ps𝒟r₂ps⋠vs) (r₁≼cus ∷ ps≼vs)
  c∉ps→𝒟-aux-pres-⋠⁻ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ 𝒟r₁ps𝒟r₂ps⋠vs (∣≼ʳ r₂≼cus ∷ ps≼vs) =
    c∉ps→𝒟-aux-pres-⋠⁻ (x∉p∪q⁻ʳ c∉r₁∪r₂) (All.++⁻ʳ _  𝒟r₁ps𝒟r₂ps⋠vs) (r₂≼cus ∷ ps≼vs)

  -- If c is not one of the root constructors of the first pattern in ps, and all rows in the default matrix do not match `vs`, all rows in the original matrix do not match `con c us ∷ vs`
  c∉pss→𝒟-pres-⋠⁻ : ∀ {pss}
    → c ∉ Σ pss
    → All (_⋠* vs) (𝒟 pss)
    → All (_⋠* con {α} c us ∷ vs) pss
  c∉pss→𝒟-pres-⋠⁻ {[]} c∉pss [] = []
  c∉pss→𝒟-pres-⋠⁻ {ps ∷ pss} c∉ps∪pss 𝒟ps𝒟pss⋠vs =
    let 𝒟ps⋠vs , 𝒟pss⋠vs = All.++⁻ (𝒟-aux ps) 𝒟ps𝒟pss⋠vs
        c∉ps , c∉pss = x∉p∪q⁻ c∉ps∪pss
     in c∉ps→𝒟-aux-pres-⋠⁻ c∉ps 𝒟ps⋠vs ∷ c∉pss→𝒟-pres-⋠⁻ c∉pss 𝒟pss⋠vs


module _ {α} {ps : Pats αs} {pss} where

  -- If Σ pss is not complete, and ps is useful wrt 𝒟 pss, ∙ ∷ ps is also useful wrt pss.
  -- That means, it suffices to check for usefulness of ps wrt 𝒟 pss if Σ pss is not complete.
  useful-∙-𝒟⁺ :
      Nonempty (∁ (Σ pss))
    → Useful ps (𝒟 pss)
    → Useful (∙ {α} ∷ ps) pss
  useful-∙-𝒟⁺ (c , c∈∁pss) (vs , ps≼vs , 𝒟pss⋠vs) =
    inhabOf c ∷ vs , ∙≼ ∷ ps≼vs , c∉pss→𝒟-pres-⋠⁻ (x∈∁p⇒x∉p c∈∁pss) 𝒟pss⋠vs

  -- ps is useful wrt (𝒟 pss) if (∙ ∷ ps) is useful wrt pss
  useful-∙-𝒟⁻ : Useful (∙ {α} ∷ ps) pss → Useful ps (𝒟 pss)
  useful-∙-𝒟⁻ (v ∷ vs , ∙≼ ∷ ps≼vs , pss⋠vvs) = vs , ps≼vs , 𝒟-pres-⋠ pss⋠vvs

--------------------------------------------------------------------------------
-- Usefulness checking algorithm

{-# TERMINATING #-}
useful? : (ps : Pats αs) (pss : PatMat αs) → Dec (Useful ps pss)
useful? [] [] = yes useful-[]-[]
useful? [] (_ ∷ _) = no ¬useful-[]-∷
useful? (∙ ∷ ps) pss with nonempty? (∁ (Σ pss))
... | yes ∃c∈∁pss =
      Dec.map′ (useful-∙-𝒟⁺ ∃c∈∁pss) useful-∙-𝒟⁻ (useful? ps (𝒟 pss))
... | no _ =
      Dec.map useful-∙-𝒮⇔ (any? λ c → useful? (All.++⁺ ∙* ps) (𝒮 c pss))
useful? (con c rs ∷ ps) pss =
  Dec.map useful-con⇔ (useful? (All.++⁺ rs ps) (𝒮 c pss))
useful? (r₁ ∣ r₂ ∷ ps) pss =
  Dec.map useful-∣⇔ (useful? (r₁ ∷ ps) pss ⊎-dec useful? (r₂ ∷ ps) pss)

exhaustive? : (pss : PatMat αs) → Exhaustive pss ⊎ NonExhaustive pss
exhaustive? pss with useful? ∙* pss
... | yes h = inj₂ (NonExhaustive′→NonExhaustive h)
... | no h = inj₁ (Exhaustive′→Exhaustive h)
