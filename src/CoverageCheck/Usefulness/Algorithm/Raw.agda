open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)

open import CoverageCheck.Usefulness.Algorithm.Types

module CoverageCheck.Usefulness.Algorithm.Raw
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    αss : TyStack
    d : NameData
    @0 α0 : Ty
    @0 αs0 βs0 : Tys
    @0 αss0 βss0 : TyStack
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Raw algorithm

module _ ⦃ sig : Signature ⦄ {d : NameData} (c : NameCon d)
  (let αs = argsTy (dataDefs sig d) c)
  where

  -- Specialization (𝒮): filters out clauses whose first pattern does not match a value of the form `con c ⋯`.

  specializeConCase : {c' : NameCon d}
    → (let @0 αs' : Tys
           αs' = argsTy (dataDefs sig d) c')
    → (rs : Patterns αs') (ps : Patterns βs0) (pss : PatternStack βss0)
    → (eq : Dec (c ≡ c'))
    → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specializeConCase rs ps pss eq =
    ifDec eq (λ where ⦃ refl ⦄ → (rs ∷ ps ∷ pss) ∷ []) []
  {-# COMPILE AGDA2HS specializeConCase inline #-}

  specialize'
    : PatternStack ((TyData d ∷ βs0) ∷ βss0)
    → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specialize' ((— ∷ ps) ∷ pss) = (—* ∷ ps ∷ pss) ∷ []
  specialize' ((con c' rs ∷ ps) ∷ pss) = specializeConCase rs ps pss (c ≟ c')
  specialize' ((r₁ ∣ r₂ ∷ ps) ∷ pss) =
    specialize' ((r₁ ∷ ps) ∷ pss) ++ specialize' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS specialize' #-}

  specialize
    : PatternStackMatrix ((TyData d ∷ βs0) ∷ βss0)
    → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specialize = concatMap specialize'
  {-# COMPILE AGDA2HS specialize #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Root constructor set: the set of constructors that appear as the outermost constructor pattern in the first column of the pattern matrix.
  -- e.g. The root constructor set is {nil, cons} for the following pattern matrix:
  --
  --   [ [ (nil ∣ cons — nil) , ─ ]
  --   , [ cons — (one —)     , — ] ]
  --

  rootConSet' : Pattern (TyData d0) → Set (NameCon d0)
  rootConSet' —         = Set.empty
  rootConSet' (con c _) = Set.singleton c
  rootConSet' (p ∣ q)   = Set.union (rootConSet' p) (rootConSet' q)
  {-# COMPILE AGDA2HS rootConSet' #-}

  rootConSet : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0) → Set (NameCon d0)
  rootConSet = foldMap (rootConSet' ∘ headAll ∘ headAll)
  {-# COMPILE AGDA2HS rootConSet #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Default matrix (𝒟): filters out clauses whose first pattern is a constructor pattern

  default' : PatternStack ((α0 ∷ αs0) ∷ αss0) → PatternStackMatrix (αs0 ∷ αss0)
  default' ((—        ∷ ps) ∷ pss) = (ps ∷ pss) ∷ []
  default' ((con c rs ∷ ps) ∷ pss) = []
  default' ((r₁ ∣ r₂  ∷ ps) ∷ pss) = default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS default' #-}

  default_ : PatternStackMatrix ((α0 ∷ αs0) ∷ αss0) → PatternStackMatrix (αs0 ∷ αss0)
  default_ = concatMap default'
  {-# COMPILE AGDA2HS default_ #-}


module _ ⦃ sig : Signature ⦄ where

  -- Is there a constructor that does not appear in root constructor set?
  existMissCon : PatternStackMatrix ((TyData d ∷ αs0) ∷ αss0) → Bool
  existMissCon psmat = not (Set.null missConSet)
    where
      conSet     = rootConSet psmat
      missConSet = Set.difference (nameConSet (dataDefs sig _)) conSet
  {-# COMPILE AGDA2HS existMissCon #-}

  -- The core usefulness checking algorithm 𝒰ʳᵉᶜ
  {-# TERMINATING #-}
  isUseful : PatternStackMatrix αss → PatternStack αss → Bool
  isUseful {[]} [] [] = True
  isUseful {[]} (_ ∷ _) [] = False
  isUseful {[] ∷ αss} psmat (_ ∷ pss) = isUseful {αss} (map tailAll psmat) pss
  isUseful {(TyData d ∷ αs) ∷ αss} psmat ((— ∷ ps) ∷ pss) =
    if existMissCon psmat
      then isUseful (default_ psmat) (ps ∷ pss)
      else anyNameCon (dataDefs sig d) λ c →
            isUseful (specialize c psmat) (—* ∷ ps ∷ pss)
  isUseful {(TyData d ∷ αs) ∷ αss} psmat ((con c rs ∷ ps) ∷ pss) =
    isUseful (specialize c psmat) (rs ∷ ps ∷ pss)
  isUseful {(TyData d ∷ αs) ∷ αss} psmat ((r₁ ∣ r₂  ∷ ps) ∷ pss) =
    isUseful psmat ((r₁ ∷ ps) ∷ pss) || isUseful psmat ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS isUseful #-}
