{-# OPTIONS --no-keep-pattern-variables #-}

open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name

module CoverageCheck.Usefulness
  {{@0 globals : Globals}}
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

module _
  {{sig : Signature}}
  {d : NameData} (c : NameCon d)
  (let αs = argsTy (dataDefs sig d) c)
  where

  -- Specialisation: filters out clauses whose first pattern does not match a value of the form `con c -`.
  specialiseAux : Patterns (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialiseAux (—         ◂ ps) = (—* ◂◂ᵖ ps) ∷ []
  specialiseAux (con c' rs ◂ ps) =
    ifDec (c ≟ c') (λ where {{refl}} → (rs ◂◂ᵖ ps) ∷ []) []
  specialiseAux (r₁ ∣ r₂   ◂ ps) = specialiseAux (r₁ ◂ ps) ++ specialiseAux (r₂ ◂ ps)
  {-# COMPILE AGDA2HS specialiseAux #-}

  specialise : PatternMatrix (TyData d ◂ βs0) → PatternMatrix (αs ◂◂ βs0)
  specialise = concatMap specialiseAux
  {-# COMPILE AGDA2HS specialise #-}


module _
  {{@0 sig : Signature}}
  where

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

  module _ {{@0 sig : Signature}} where

    infix 4 elemRootCons

    elemRootCons : (c : NameCon d0) (p : Pattern (TyData d0)) → Bool
    syntax elemRootCons c p = c ∈ᵇ p
    c ∈ᵇ —         = False
    c ∈ᵇ con c' ps = value (c ≟ c')
    c ∈ᵇ (p ∣ q)   = c ∈ᵇ p || c ∈ᵇ q
    {-# COMPILE AGDA2HS elemRootCons #-}


  module _ {{sig : Signature}} {d : NameData} where

    -- Is there a constructor that does not appear in the first column of P?
    existsMissingCon : (P : PatternMatrix (TyData d ◂ αs0)) → Bool
    existsMissingCon pss =
      not (allNameCon (dataDefs sig d) λ c → any (λ ps → c ∈ᵇ headPattern ps) pss)
    {-# COMPILE AGDA2HS existsMissingCon #-}


  module _ {{sig : Signature}} where

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

module _ {{@0 sig : Signature}} where

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


module _
  {{@0 sig : Signature}}
  {{nonEmptyAxiom : ∀ {α} → Value α}}
  where

  inhabCon : (d : NameData) → NameCon d
  inhabCon d = case nonEmptyAxiom {α = TyData d} of λ { (con c _) → c }
  {-# COMPILE AGDA2HS inhabCon #-}


module _
  {{sig : Signature}}
  {d : NameData}
  where

  -- Is there a constructor that does not appear in the first column of P?
  decExistsMissingCon : (P : PatternMatrix (TyData d ◂ αs0))
    → Either
        (Erase (∃[ c ∈ _ ] All (λ ps → c ∉ headPattern ps) P))
        (Erase (∀ c → Any (λ ps → c ∈ headPattern ps) P))
  decExistsMissingCon pss =
    case
      decAllNameCon (dataDefs sig d) (λ c →
        anyDec (λ ps → c ∈? headPattern ps) pss)
    of λ
      { (Left (Erased h)) → Right (Erased h)
      ; (Right (Erased (c ⟨ h ⟩ ))) → Left (Erased (c ⟨ ¬Any⇒All¬ pss h ⟩))
      }
  {-# COMPILE AGDA2HS decExistsMissingCon #-}

module _ {{@0 sig : Signature}} where

  record Usefulness
    (u : ∀ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set)
    : Set where
    field
      nilNil : u [] ⌈⌉
      @0 consNil : {ps : Patterns ⌈⌉} {pss : PatternMatrix ⌈⌉} → ¬ u (ps ∷ pss) ⌈⌉

      orHead : {pss : PatternMatrix (α ◂ αs)} {r₁ r₂ : Pattern α} {ps : Patterns αs}
        → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps)) → u pss (r₁ ∣ r₂ ◂ ps)
      @0 orHeadInv : {pss : PatternMatrix (α ◂ αs)} {r₁ r₂ : Pattern α} {ps : Patterns αs}
        → u pss (r₁ ∣ r₂ ◂ ps) → Either (u pss (r₁ ◂ ps)) (u pss (r₂ ◂ ps))

      conHead : {pss : PatternMatrix (TyData d ◂ βs)} {c : NameCon d}
        (let αs = argsTy (dataDefs sig d) c)
        {rs : Patterns αs} {ps : Patterns βs}
        → u (specialise c pss) (rs ◂◂ᵖ ps) → u pss (con c rs ◂ ps)
      @0 conHeadInv : {pss : PatternMatrix (TyData d ◂ βs)} {c : NameCon d}
        (let αs = argsTy (dataDefs sig d) c)
        {rs : Patterns αs} {ps : Patterns βs}
        → u pss (con c rs ◂ ps) → u (specialise c pss) (rs ◂◂ᵖ ps)

      wildHeadMiss : {pss : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
        → @0 ∃[ c ∈ _ ] All (λ ps → c ∉ headPattern ps) pss
        → u (default' pss) ps
        → u pss (— ◂ ps)
      @0 wildHeadMissInv : {pss : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
        → @0 ∃[ c ∈ _ ] All (λ ps → c ∉ headPattern ps) pss
        → u pss (— ◂ ps)
        → u (default' pss) ps

      wildHeadComp : {pss : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
        → @0 (∀ c → Any (λ ps → c ∈ headPattern ps) pss)
        → Σ[ c ∈ NameCon d ] u (specialise c pss) (—* ◂◂ᵖ ps)
        → u pss (— ◂ ps)
      @0 wildHeadCompInv : {pss : PatternMatrix (TyData d ◂ αs)} {ps : Patterns αs}
        → (∀ c → Any (λ ps → c ∈ headPattern ps) pss)
        → u pss (— ◂ ps)
        → Σ[ c ∈ NameCon d ] u (specialise c pss) (—* ◂◂ᵖ ps)

  open Usefulness {{...}} public
  {-# COMPILE AGDA2HS Usefulness class #-}


module _ {{@0 sig : Signature}} where

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
  {{sig : Signature}}
  (u : ∀ {@0 αs0} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set)
  {{_ : Usefulness u}}
  {{nonEmptyAxiom : ∀ {α} → Value α}}
  where

  decUseful : (P : PatternMatrix αs) (ps : Patterns αs) → @0 UsefulAcc P ps → DecP (u P ps)
  decUseful {⌈⌉}            []      ⌈⌉              done             = Yes nilNil
  decUseful {⌈⌉}            (_ ∷ _) ⌈⌉              done             = No consNil
  decUseful {TyData d ◂ αs} pss     (— ◂ ps)        (step-wild h h') =
    case decExistsMissingCon pss of λ
      { (Left (Erased miss))  →
          mapDecP (wildHeadMiss miss) (wildHeadMissInv miss)
            (decUseful (default' pss) ps (h miss))
      ; (Right (Erased comp)) →
          mapDecP (wildHeadComp comp) (wildHeadCompInv comp)
            (decPAnyNameCon (dataDefs sig d) λ c →
              decUseful (specialise c pss) (—* ◂◂ᵖ ps) (h' c (comp c)))
      }
  decUseful {TyData d ◂ αs} pss     (con c rs ◂ ps) (step-con h)     =
    mapDecP conHead conHeadInv (decUseful (specialise c pss) (rs ◂◂ᵖ ps) h)
  decUseful {TyData d ◂ αs} pss     (r₁ ∣ r₂  ◂ ps) (step-∣ h h')    =
    mapDecP orHead orHeadInv
      (eitherDecP (decUseful pss (r₁ ◂ ps) h) (decUseful pss (r₂ ◂ ps) h'))
  {-# COMPILE AGDA2HS decUseful #-}

--------------------------------------------------------------------------------
-- Usefulness

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
Useful : {{@0 sig : Signature}} (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) → Set
Useful {αs0} P ps = ∃[ vs ∈ Values αs0 ] (P ⋠** vs × ps ≼* vs)
{-# COMPILE AGDA2HS Useful inline #-}

--------------------------------------------------------------------------------
-- Properties of ≼ and specialise/default

-- module _ {c : Con α} {us : Vals (argsTy α c)} {vs : Vals αs} where

--   specialiseAux-preserves-≼ : {ps : Pats (α ∷ αs)}
--     → ps ≼* con {α} c us ∷ vs
--     → specialiseAux c ps ≼** (us ++ᵥ vs)
--   specialiseAux-preserves-≼ {∙ ∷ ps} ∙ps≼cusvs = here (∙≼*⁻ ∙ps≼cusvs)
--   specialiseAux-preserves-≼ {con d rs ∷ ps} drsps≼cusvs with c ≟Fin d
--   ... | no c≢d = contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c≢d
--   ... | yes refl = here (con≼*⁻ drsps≼cusvs)
--   specialiseAux-preserves-≼ {r₁ ∣ r₂ ∷ ps} =
--     [ ++Any⁺ˡ , ++Any⁺ʳ _ ] ∘
--     map-⊎ specialiseAux-preserves-≼ specialiseAux-preserves-≼ ∘
--     ∣≼*⁻

--   -- specialise preserves ≼
--   specialise-preserves-≼ : {P : PatMat (α ∷ αs)}
--     → P ≼** con {α} c us ∷ vs
--     → specialise c P ≼** (us ++ᵥ vs)
--   specialise-preserves-≼ = concatAny⁺ ∘ gmapAny specialiseAux-preserves-≼

--   specialiseAux-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
--     → specialiseAux c ps ≼** (us ++ᵥ vs)
--     → ps ≼* con {α} c us ∷ vs
--   specialiseAux-preserves-≼⁻ {∙ ∷ ps} (here ∙*ps≼usvs) = ∙≼*⁺ ∙*ps≼usvs
--   specialiseAux-preserves-≼⁻ {con d rs ∷ ps} _ with c ≟Fin d
--   specialiseAux-preserves-≼⁻ {con d rs ∷ ps} (here drsps≼cusvs) | yes refl = con≼*⁺ drsps≼cusvs
--   specialiseAux-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
--     ∣≼*⁺ ∘ map-⊎ specialiseAux-preserves-≼⁻ specialiseAux-preserves-≼⁻ ∘ ++Any⁻ _

--   -- Unspecialisation preserves ≼
--   specialise-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
--     → specialise c P ≼** (us ++ᵥ vs)
--     → P ≼** con {α} c us ∷ vs
--   specialise-preserves-≼⁻ = mapAny specialiseAux-preserves-≼⁻ ∘ mapAny⁻ ∘ concatAny⁻ _

--   specialise-preserves-≼⇔ : {P : PatMat (α ∷ αs)}
--     → P ≼** con {α} c us ∷ vs ⇔ specialise c P ≼** (us ++ᵥ vs)
--   specialise-preserves-≼⇔ = mk⇔ specialise-preserves-≼ specialise-preserves-≼⁻


-- module _ {c : Con α} {us : Vals (argsTy α c)} {vs : Vals αs} where

--   defaultAux-preserves-≼ : {ps : Pats (α ∷ αs)}
--     → c ∉ headAll ps
--     → ps ≼* con {α} c us ∷ vs
--     → defaultAux ps ≼** vs
--   defaultAux-preserves-≼ {∙ ∷ ps} _ ∙ps≼cusvs = here (∷⁻ ∙ps≼cusvs .proj₂)
--   defaultAux-preserves-≼ {con d rs ∷ ps} c∉d drsps≼cusvs =
--     contradiction (sym (c≼d→c≡d (∷⁻ drsps≼cusvs .proj₁))) c∉d
--   defaultAux-preserves-≼ {r₁ ∣ r₂ ∷ ps} c∉r₁∪r₂ =
--     [ ++Any⁺ˡ , ++Any⁺ʳ _ ] ∘
--     map-⊎
--       (defaultAux-preserves-≼ (c∉r₁∪r₂ ∘ inj₁))
--       (defaultAux-preserves-≼ (c∉r₁∪r₂ ∘ inj₂)) ∘
--     ∣≼*⁻

--   -- If c does not appear in the first column of P, default preserves ≼
--   default-preserves-≼ : {P : PatMat (α ∷ αs)}
--     → All (λ ps → c ∉ headAll ps) P
--     → P ≼** con {α} c us ∷ vs
--     → default P ≼** vs
--   default-preserves-≼ {ps ∷ P} (c∉ps ∷ _) (here ps≼cusvs) =
--     ++Any⁺ˡ (defaultAux-preserves-≼ c∉ps ps≼cusvs)
--   default-preserves-≼ {ps ∷ P} (_ ∷ c∉P) (there P≼cusvs) =
--     ++Any⁺ʳ _ (default-preserves-≼ c∉P P≼cusvs)


-- module _ {v : Val α} {vs : Vals αs} where

--   defaultAux-preserves-≼⁻ : {ps : Pats (α ∷ αs)}
--     → defaultAux ps ≼** vs
--     → ps ≼* v ∷ vs
--   defaultAux-preserves-≼⁻ {∙ ∷ ps} (here ∙ps≼vvs) = ∙≼ ∷ ∙ps≼vvs
--   defaultAux-preserves-≼⁻ {r₁ ∣ r₂ ∷ ps} =
--     ∣≼*⁺ ∘ map-⊎ defaultAux-preserves-≼⁻ defaultAux-preserves-≼⁻ ∘ ++Any⁻ _

--   default-preserves-≼⁻ : {P : PatMat (α ∷ αs)}
--     → default P ≼** vs
--     → P ≼** v ∷ vs
--   default-preserves-≼⁻ = mapAny defaultAux-preserves-≼⁻ ∘ mapAny⁻ ∘ concatAny⁻ _

-- --------------------------------------------------------------------------------
-- -- Properties of usefulness

-- -- [] is useful wrt []
-- useful-[]-[] : Useful [] []
-- useful-[]-[] = [] , (λ ()) , []

-- -- [] is not wrt any non-empty matrix
-- ¬useful-∷-[] : {ps : Pats []} {P : PatMat []} → ¬ Useful (ps ∷ P) []
-- ¬useful-∷-[] {[]} ([] , []P⋠[] , _) = []P⋠[] (here [])

-- module _ {P : PatMat (α ∷ αs)} {r₁ r₂ : Pat α} {ps : Pats αs} where

--   merge-useful : Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps) → Useful P (r₁ ∣ r₂ ∷ ps)
--   merge-useful (inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)) =
--     vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs
--   merge-useful (inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)) =
--     vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs

--   merge-useful⁻ : Useful P (r₁ ∣ r₂ ∷ ps) → Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)
--   merge-useful⁻ (vvs , P⋠vvs , ∣≼ˡ r₁≼v ∷ ps≼vs) =
--     inj₁ (vvs , P⋠vvs , r₁≼v ∷ ps≼vs)
--   merge-useful⁻ (vvs , P⋠vvs , ∣≼ʳ r₂≼v ∷ ps≼vs) =
--     inj₂ (vvs , P⋠vvs , r₂≼v ∷ ps≼vs)

--   -- (r₁ ∣ r₂ ∷ ps) is useful wrt P iff (r₁ ∷ ps) or (r₂ ∷ ps) is useful wrt P
--   merge-useful⇔ : (Useful P (r₁ ∷ ps) ⊎ Useful P (r₂ ∷ ps)) ⇔ Useful P (r₁ ∣ r₂ ∷ ps)
--   merge-useful⇔ = mk⇔ merge-useful merge-useful⁻


-- module _ {P : PatMat (α ∷ αs)} {c : Con α} {rs : Pats (argsTy α c)} {ps : Pats αs} where

--   specialise-preserves-usefulness-con :
--       Useful P (con c rs ∷ ps)
--     → Useful (specialise c P) (++All⁺ rs ps)
--   specialise-preserves-usefulness-con (con c vs ∷ us , P⋠cvsus , con≼ rs≼vs ∷ ps≼us) =
--     ++All⁺ vs us , contraposition specialise-preserves-≼⁻ P⋠cvsus , ++⁺ rs≼vs ps≼us

--   specialise-preserves-usefulness-con⁻ :
--       Useful (specialise c P) (++All⁺ rs ps)
--     → Useful P (con c rs ∷ ps)
--   specialise-preserves-usefulness-con⁻ (usvs , specialiseP⋠usvs , rsps≼usvs)
--     with us , vs , refl , rs≼us , ps≼vs ← split rs rsps≼usvs =
--     con c us ∷ vs , contraposition specialise-preserves-≼ specialiseP⋠usvs , con≼ rs≼us ∷ ps≼vs

--   -- con c rs ∷ ps is useful wrt P iff rs ++ ps is useful wrt specialise c P
--   specialise-preserves-usefulness-con⇔ :
--       Useful (specialise c P) (++All⁺ rs ps)
--     ⇔ Useful P (con c rs ∷ ps)
--   specialise-preserves-usefulness-con⇔ =
--     mk⇔ specialise-preserves-usefulness-con⁻ specialise-preserves-usefulness-con


-- module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

--   -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialise c P`
--   ∃specialise-preserves-usefulness-∙ :
--       Useful P (∙ ∷ ps)
--     → ∃[ c ] Useful (specialise c P) (++All⁺ ∙* ps)
--   ∃specialise-preserves-usefulness-∙ (con c us ∷ vs , P⋠cusvs , ∙≼ ∷ ps≼vs) =
--     c , ++All⁺ us vs , contraposition specialise-preserves-≼⁻ P⋠cusvs , ++⁺ ∙*≼ ps≼vs

--   -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialise c P`, `∙ ∷ ps` is also useful wrt P
--   ∃specialise-preserves-usefulness-∙⁻ :
--       ∃[ c ] Useful (specialise c P) (++All⁺ ∙* ps)
--     → Useful P (∙ ∷ ps)
--   ∃specialise-preserves-usefulness-∙⁻ (c , usvs , specialiseP⋠usvs , ∙*ps≼usvs)
--     with us , vs , refl , _ , ps≼vs ← split {argsTy α c} ∙* ∙*ps≼usvs =
--     con c us ∷ vs , contraposition specialise-preserves-≼ specialiseP⋠usvs , ∙≼ ∷ ps≼vs

--   -- ∙ ∷ ps is useful wrt P iff ∙* ++ ps is useful wrt specialise c P
--   ∃specialise-preserves-usefulness-∙⇔ :
--       (∃[ c ] Useful (specialise c P) (++All⁺ ∙* ps))
--     ⇔ Useful P (∙ ∷ ps)
--   ∃specialise-preserves-usefulness-∙⇔ =
--     mk⇔ ∃specialise-preserves-usefulness-∙⁻ ∃specialise-preserves-usefulness-∙


-- module _ {P : PatMat (α ∷ αs)} {ps : Pats αs} where

--   -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
--   default-preserves-usefulness : Useful P (∙ ∷ ps) → Useful (default P) ps
--   default-preserves-usefulness (v ∷ vs  , P⋠vvs , ∙≼ ∷ ps≼vs) =
--     vs , contraposition default-preserves-≼⁻ P⋠vvs , ps≼vs

--   -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
--   default-preserves-usefulness⁻ : Missing P → Useful (default P) ps → Useful P (∙ ∷ ps)
--   default-preserves-usefulness⁻ (c , c∉P) (vs , defaultP⋠vs , ps≼vs) =
--     inhabOf c ∷ vs , contraposition (default-preserves-≼ c∉P) defaultP⋠vs , ∙≼ ∷ ps≼vs

--   default-preserves-usefulness⇔ : Missing P → Useful (default P) ps ⇔ Useful P (∙ ∷ ps)
--   default-preserves-usefulness⇔ ∃c∉P =
--     mk⇔ (default-preserves-usefulness⁻ ∃c∉P) default-preserves-usefulness

-- --------------------------------------------------------------------------------
-- -- Usefulness checking algorithm

-- useful?′ : (P : PatMat αs) (ps : Pats αs) → UsefulAcc P ps → Dec (Useful P ps)
-- useful?′ P (∙ ∷ qs) (step-∙ h h′) with ∃missingCon? P
-- ... | inj₁ ∃c∉P =
--       mapDec (default-preserves-usefulness⇔ ∃c∉P) (useful?′ (default P) qs (h ∃c∉P))
-- ... | inj₂ ∀c∈P =
--       mapDec ∃specialise-preserves-usefulness-∙⇔
--         (anyFin? λ c → useful?′ (specialise c P) (++All⁺ ∙* qs) (h′ c (∀c∈P c)))
-- useful?′ P (con c rs ∷ ps) (step-con h) =
--   mapDec specialise-preserves-usefulness-con⇔
--     (useful?′ (specialise c P) (++All⁺ rs ps) h)
-- useful?′ P (r₁ ∣ r₂ ∷ ps) (step-∣ h h′) =
--   mapDec merge-useful⇔
--     (useful?′ P (r₁ ∷ ps) h ⊎-dec useful?′ P (r₂ ∷ ps) h′)
-- useful?′ [] [] _ = yes useful-[]-[]
-- useful?′ (_ ∷ _) [] _ = no ¬useful-∷-[]

-- --------------------------------------------------------------------------------
-- -- Termination

-- {-

--        | ps size + P size | αs len |
-- -------+------------------+--------+
-- wild 1 |    = + ≤ ⇒ ≤     |   <    |
-- wild 2 |    = + < ⇒ <     |  <=>   |
-- con    |    < + ≤ ⇒ <     |  <=>   |
-- or     |    < + = ⇒ <     |   =    |

-- -}

-- patsSize : Pats αs → ℕ → ℕ
-- patsSize [] n = n
-- patsSize (∙ ∷ ps) n = patsSize ps n
-- patsSize (con _ rs ∷ ps) n = suc (patsSize rs (patsSize ps n))
-- patsSize (r₁ ∣ r₂ ∷ ps) n = suc (patsSize (r₁ ∷ ps) n + patsSize (r₂ ∷ ps) n)

-- patMatSize : PatMat αs → ℕ
-- patMatSize P = sumList (mapList (flip patsSize 0) P)

-- patsSize-++ : (ps : Pats αs) (qs : Pats βs) (n : ℕ)
--   → patsSize (++All⁺ ps qs) n ≡ patsSize ps (patsSize qs n)
-- patsSize-++ [] qs n = refl
-- patsSize-++ (∙ ∷ ps) qs n = patsSize-++ ps qs n
-- patsSize-++ (con _ rs ∷ ps) qs n = cong (suc ∘ patsSize rs) (patsSize-++ ps qs n)
-- patsSize-++ (r₁ ∣ r₂ ∷ ps) qs n = cong suc (cong₂ _+_ (patsSize-++ (r₁ ∷ ps) qs n) (patsSize-++ (r₂ ∷ ps) qs n))

-- patsSize∙* : ∀ αs n → patsSize (∙* {αs = αs}) n ≡ n
-- patsSize∙* [] n = refl
-- patsSize∙* (α ∷ αs) n = patsSize∙* αs n

-- patMatSize-++ : (P Q : PatMat αs) → patMatSize (P ++ Q) ≡ patMatSize P + patMatSize Q
-- patMatSize-++ P Q
--   rewrite map-++ (flip patsSize 0) P Q
--   | sum-++ (mapList (flip patsSize 0) P) (mapList (flip patsSize 0) Q)
--   = refl

-- specialiseAux-≤ : (c : Con α) (ps : Pats (α ∷ αs)) → patMatSize (specialiseAux c ps) ≤ patsSize ps 0
-- specialiseAux-≤ {α} c (∙ ∷ ps)
--   rewrite patsSize-++ (∙* {αs = argsTy α c}) ps 0
--   | patsSize∙* (argsTy α c) (patsSize ps 0)
--   | +-identityʳ (patsSize ps 0)
--   = ≤-refl
-- specialiseAux-≤ c (con c′ rs ∷ ps) with c ≟Fin c′
-- ... | yes refl
--         rewrite patsSize-++ rs ps 0
--         | +-identityʳ (patsSize rs (patsSize ps 0))
--         = n≤1+n (patsSize rs (patsSize ps 0))
-- ... | no _ = <⇒≤ 0<1+n
-- specialiseAux-≤ c (r₁ ∣ r₂ ∷ ps) =
--   -- rewrite messed up termination check, so do it manually
--   begin
--     patMatSize (specialiseAux c (r₁ ∷ ps) ++ specialiseAux c (r₂ ∷ ps))
--   ≡⟨ patMatSize-++ (specialiseAux c (r₁ ∷ ps)) (specialiseAux c (r₂ ∷ ps)) ⟩
--     patMatSize (specialiseAux c (r₁ ∷ ps)) + patMatSize (specialiseAux c (r₂ ∷ ps))
--   ≤⟨ +-mono-≤ (specialiseAux-≤ c (r₁ ∷ ps)) (specialiseAux-≤ c (r₂ ∷ ps)) ⟩
--     patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0
--   <⟨ n<1+n _ ⟩
--     suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
--   ∎
--   where open ≤-Reasoning

-- -- specialise does not increase the pattern matrix size
-- specialise-≤ : (c : Con α) (P : PatMat (α ∷ αs)) → patMatSize (specialise c P) ≤ patMatSize P
-- specialise-≤ c [] = ≤-refl
-- specialise-≤ c (ps ∷ P)
--   rewrite patMatSize-++ (specialiseAux c ps) (specialise c P)
--   = +-mono-≤ (specialiseAux-≤ c ps) (specialise-≤ c P)

-- ∈⇒specialiseAux-< : (c : Con α) (ps : Pats (α ∷ αs))
--   → c ∈ headAll ps
--   → patMatSize (specialiseAux c ps) < patsSize ps 0
-- ∈⇒specialiseAux-< c (con d rs ∷ ps) c≡d with c ≟Fin d
-- ... | yes refl
--       rewrite patsSize-++ rs ps 0
--       | +-identityʳ (patsSize rs (patsSize ps 0))
--       = ≤-refl
-- ... | no c≢d = contradiction c≡d c≢d
-- ∈⇒specialiseAux-< c (r₁ ∣ r₂ ∷ ps) (inj₁ c∈r₁) =
--   begin
--     suc (patMatSize (specialiseAux c (r₁ ∷ ps) ++ specialiseAux c (r₂ ∷ ps)))
--   ≡⟨ cong suc (patMatSize-++ (specialiseAux c (r₁ ∷ ps)) (specialiseAux c (r₂ ∷ ps))) ⟩
--     suc (patMatSize (specialiseAux c (r₁ ∷ ps)) + patMatSize (specialiseAux c (r₂ ∷ ps)))
--   <⟨ s<s (+-mono-<-≤ (∈⇒specialiseAux-< c (r₁ ∷ ps) c∈r₁) (specialiseAux-≤ c (r₂ ∷ ps))) ⟩
--     suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
--   ∎
--   where open ≤-Reasoning
-- ∈⇒specialiseAux-< c (r₁ ∣ r₂ ∷ ps) (inj₂ c∈r₂) =
--   begin
--     suc (patMatSize (specialiseAux c (r₁ ∷ ps) ++ specialiseAux c (r₂ ∷ ps)))
--   ≡⟨ cong suc (patMatSize-++ (specialiseAux c (r₁ ∷ ps)) (specialiseAux c (r₂ ∷ ps))) ⟩
--     suc (patMatSize (specialiseAux c (r₁ ∷ ps)) + patMatSize (specialiseAux c (r₂ ∷ ps)))
--   <⟨ s<s (+-mono-≤-< (specialiseAux-≤ c (r₁ ∷ ps)) (∈⇒specialiseAux-< c (r₂ ∷ ps) c∈r₂)) ⟩
--     suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
--   ∎
--   where open ≤-Reasoning

-- -- specialise strictly reduces the pattern matrix size if the constructor is in the first column of the matrix
-- ∈⇒specialise-< : (c : Con α) (P : PatMat (α ∷ αs))
--   → Any (λ ps → c ∈ headAll ps) P
--   → patMatSize (specialise c P) < patMatSize P
-- ∈⇒specialise-< c (ps ∷ P) (here c∈ps)
--   rewrite patMatSize-++ (specialiseAux c ps) (specialise c P)
--   = +-mono-<-≤ (∈⇒specialiseAux-< c ps c∈ps) (specialise-≤ c P)
-- ∈⇒specialise-< c (ps ∷ P) (there c∈P)
--   rewrite patMatSize-++ (specialiseAux c ps) (specialise c P)
--   = +-mono-≤-< (specialiseAux-≤ c ps) (∈⇒specialise-< c P c∈P)

-- defaultAux-≤ : (ps : Pats (α ∷ αs)) → patMatSize (defaultAux ps) ≤ patsSize ps 0
-- defaultAux-≤ (∙ ∷ ps)
--   rewrite +-identityʳ (patsSize ps 0)
--   = ≤-refl
-- defaultAux-≤ (con _ _ ∷ ps) = <⇒≤ 0<1+n
-- defaultAux-≤ (r₁ ∣ r₂ ∷ ps) =
--   begin
--     patMatSize (defaultAux (r₁ ∷ ps) ++ defaultAux (r₂ ∷ ps))
--   ≡⟨ patMatSize-++ (defaultAux (r₁ ∷ ps)) (defaultAux (r₂ ∷ ps)) ⟩
--     patMatSize (defaultAux (r₁ ∷ ps)) + patMatSize (defaultAux (r₂ ∷ ps))
--   ≤⟨ +-mono-≤ (defaultAux-≤ (r₁ ∷ ps)) (defaultAux-≤ (r₂ ∷ ps)) ⟩
--     patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0
--   <⟨ n<1+n _ ⟩
--     suc (patsSize (r₁ ∷ ps) 0 + patsSize (r₂ ∷ ps) 0)
--   ∎
--   where open ≤-Reasoning

-- -- default does not increase the pattern matrix size
-- default-≤ : (P : PatMat (α ∷ αs)) → patMatSize (default P) ≤ patMatSize P
-- default-≤ [] = ≤-refl
-- default-≤ (ps ∷ P)
--   rewrite patMatSize-++ (defaultAux ps) (default P)
--   = +-mono-≤ (defaultAux-≤ ps) (default-≤ P)

-- SomeProblem : Set
-- SomeProblem = ∃[ αs ] PatMat αs × Pats αs

-- problemSize : SomeProblem → ℕ × ℕ
-- problemSize (αs , P , ps) = (patMatSize P + patsSize ps 0) , length αs

-- -- Lexicographic ordering on SomeProblem
-- _⊏_ : (P Q : SomeProblem) → Set
-- _⊏_ = ×-Lex _≡_ _<_ _<_ on problemSize

-- -- _⊏_ is well-founded
-- ⊏-wellFounded : WellFounded _⊏_
-- ⊏-wellFounded = on-wellFounded problemSize (×-wellFounded <-wellFounded <-wellFounded)

-- -- specialise strictly reduces the problem size
-- specialise-⊏ : (P : PatMat (α ∷ αs)) (c : Con α) (rs : Pats (argsTy α c)) (ps : Pats αs)
--   → (-, specialise c P , ++All⁺ rs ps) ⊏ (-, P , con c rs ∷ ps)
-- specialise-⊏ P c rs ps
--   rewrite patsSize-++ rs ps 0
--   = inj₁ (+-mono-≤-< (specialise-≤ c P) (n<1+n _))

-- -- default strictly reduces the problem size
-- default-⊏ : (P : PatMat (α ∷ αs)) (qs : Pats αs)
--   → (-, default P , qs) ⊏ (-, P , ∙ ∷ qs)
-- default-⊏ P qs with m≤n⇒m<n∨m≡n (default-≤ P)
-- ... | inj₁ defaultP<P = inj₁ (+-monoˡ-< (patsSize qs 0) defaultP<P)
-- ... | inj₂ defaultP≡P = inj₂ (cong (_+ patsSize qs 0) defaultP≡P , n<1+n _)

-- -- specialise strictly reduces the problem size if the constructor is in the first column of the matrix
-- ∈⇒specialise-⊏ : (c : Con α) (P : PatMat (α ∷ αs)) (qs : Pats αs)
--   → Any (λ ps → c ∈ headAll ps) P
--   → (-, specialise c P , ++All⁺ ∙* qs) ⊏ (-, P , ∙ ∷ qs)
-- ∈⇒specialise-⊏ {α} c P qs c∈P
--   rewrite patsSize-++ (∙* {αs = argsTy α c}) qs 0
--   | patsSize∙* (argsTy α c) (patsSize qs 0)
--   = inj₁ (+-monoˡ-< (patsSize qs 0) (∈⇒specialise-< c P c∈P))

-- -- Choosing the left pattern strictly reduces the problem size
-- ∣-⊏ₗ : (P : PatMat (α ∷ αs)) (r₁ r₂ : Pat α) (ps : Pats αs)
--   → (_ , P , r₁ ∷ ps) ⊏ (_ , P , r₁ ∣ r₂ ∷ ps)
-- ∣-⊏ₗ P r₁ r₂ ps =
--   inj₁ (+-monoʳ-< (patMatSize P) (m≤m+n (suc (patsSize (r₁ ∷ ps) 0)) (patsSize (r₂ ∷ ps) 0)))

-- -- Choosing the right pattern strictly reduces the problem size
-- ∣-⊏ᵣ : (P : PatMat (α ∷ αs)) (r₁ r₂ : Pat α) (ps : Pats αs)
--   → (_ , P , r₂ ∷ ps) ⊏ (_ , P , r₁ ∣ r₂ ∷ ps)
-- ∣-⊏ᵣ P r₁ r₂ ps =
--   inj₁ (+-monoʳ-< (patMatSize P) (s<s (m≤n+m (patsSize (r₂ ∷ ps) 0) (patsSize (r₁ ∷ ps) 0))))

-- ∀UsefulAccAux : (P : PatMat αs) (ps : Pats αs)
--   → Acc _⊏_ (-, P , ps)
--   → UsefulAcc P ps
-- ∀UsefulAccAux P [] _ = done
-- ∀UsefulAccAux P (∙ ∷ ps) (acc h) =
--   step-∙
--     (λ _ → ∀UsefulAccAux (default P) ps (h (default-⊏ P ps)))
--     (λ c c∈P → ∀UsefulAccAux (specialise c P) (++All⁺ ∙* ps) (h (∈⇒specialise-⊏ c P ps c∈P)))
-- ∀UsefulAccAux P (con c rs ∷ ps) (acc h) =
--   step-con (∀UsefulAccAux (specialise c P) (++All⁺ rs ps) (h (specialise-⊏ P c rs ps)))
-- ∀UsefulAccAux P (r₁ ∣ r₂ ∷ ps) (acc h) =
--   step-∣
--     (∀UsefulAccAux P (r₁ ∷ ps) (h (∣-⊏ₗ P r₁ r₂ ps)))
--     (∀UsefulAccAux P (r₂ ∷ ps) (h (∣-⊏ᵣ P r₁ r₂ ps)))

-- ∀UsefulAcc : (P : PatMat αs) (ps : Pats αs) → UsefulAcc P ps
-- ∀UsefulAcc P ps = ∀UsefulAccAux P ps (⊏-wellFounded _)

-- --------------------------------------------------------------------------------
-- -- Entrypoint

-- useful? : (P : PatMat αs) (ps : Pats αs) → Dec (Useful P ps)
-- useful? P ps = useful?′ P ps (∀UsefulAcc P ps)
