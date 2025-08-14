open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm

module CoverageCheck.Usefulness.Usefulness1
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

module _ ⦃ @0 sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  inhab : (d : NameData) → Σ[ c ∈ NameCon d ] Values (argsTy (dataDefs sig d) c)
  inhab d = case nonEmptyAxiom {α = TyData d} of λ where
    (con c vs) → c , vs
  {-# COMPILE AGDA2HS inhab #-}

  inhabCon : (d : NameData) → NameCon d
  inhabCon d = let c , _ = inhab d in c
  {-# COMPILE AGDA2HS inhabCon inline #-}

  inhabArgs : (d : NameData) → Values (argsTy (dataDefs sig d) (inhabCon d))
  inhabArgs d = let _ , vs = inhab d in vs
  {-# COMPILE AGDA2HS inhabArgs inline #-}

--------------------------------------------------------------------------------
-- Usefulness

-- ps is useful with respect to P if
--   1. there is a list of values that matches ps (say vs)
--   2. vs does not match any row in P
-- Usefulness can also be used to formulate redundancy
record Useful ⦃ @0 sig : Signature ⦄ (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) : Set where
  field
    witness : Values αs0
    @0 P⋠witness : P ⋠** witness
    @0 witness≼ps : ps ≼* witness
open Useful public
{-# COMPILE AGDA2HS Useful newtype #-}

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

--------------------------------------------------------------------------------
-- Properties of usefulness

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
