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

  -- Specialization: filters out clauses whose first pattern does not match a value of the form `con c -`.

  specializeConCase : {c' : NameCon d}
    (let @0 αs' : Tys
         αs' = argsTy (dataDefs sig d) c')
    (rs : Patterns αs') (ps : Patterns βs0) (pss : PatternStack βss0)
    (eq : Dec (c ≡ c'))
    → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specializeConCase rs ps pss eq =
    ifDec eq (λ where ⦃ refl ⦄ → (rs ∷ ps ∷ pss) ∷ []) []
  {-# COMPILE AGDA2HS specializeConCase inline #-}

  specialize' : PatternStack ((TyData d ∷ βs0) ∷ βss0) → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specialize' ((—         ∷ ps) ∷ pss) = (—* ∷ ps ∷ pss) ∷ []
  specialize' ((con c' rs ∷ ps) ∷ pss) = specializeConCase rs ps pss (c ≟ c')
  specialize' ((r₁ ∣ r₂   ∷ ps) ∷ pss) = specialize' ((r₁ ∷ ps) ∷ pss) ++ specialize' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS specialize' #-}

  specialize : PatternStackMatrix ((TyData d ∷ βs0) ∷ βss0) → PatternStackMatrix (αs ∷ βs0 ∷ βss0)
  specialize = concatMap specialize'
  {-# COMPILE AGDA2HS specialize #-}


module _ ⦃ @0 sig : Signature ⦄ where

  rootConSet' : (p : Pattern (TyData d0)) → Set (NameCon d0)
  rootConSet' —         = Set.empty
  rootConSet' (con c _) = Set.singleton c
  rootConSet' (p ∣ q)   = Set.union (rootConSet' p) (rootConSet' q)
  {-# COMPILE AGDA2HS rootConSet' #-}

  rootConSet : (P : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)) → Set (NameCon d0)
  rootConSet psss = foldr (λ pss → Set.union (rootConSet' (headAll (headAll pss)))) Set.empty psss
  {-# COMPILE AGDA2HS rootConSet #-}


module _ ⦃ @0 sig : Signature ⦄ where

  -- Default matrix: filters out clauses whose first pattern is a constructor pattern
  default' : PatternStack ((α0 ∷ αs0) ∷ αss0) → PatternStackMatrix (αs0 ∷ αss0)
  default' ((—        ∷ ps) ∷ pss) = (ps ∷ pss) ∷ []
  default' ((con c rs ∷ ps) ∷ pss) = []
  default' ((r₁ ∣ r₂  ∷ ps) ∷ pss) = default' ((r₁ ∷ ps) ∷ pss) ++ default' ((r₂ ∷ ps) ∷ pss)
  {-# COMPILE AGDA2HS default' #-}

  default_ : PatternStackMatrix ((α0 ∷ αs0) ∷ αss0) → PatternStackMatrix (αs0 ∷ αss0)
  default_ = concatMap default'
  {-# COMPILE AGDA2HS default_ #-}


module _ ⦃ sig : Signature ⦄ where

  -- Is there a constructor that does not appear in the first column of P?
  existMissCon : (P : PatternStackMatrix ((TyData d ∷ αs0) ∷ αss0)) → Bool
  existMissCon {d = d} psss = not (Set.null missConSet)
    where
      conSet missConSet : Set (NameCon d)
      conSet     = rootConSet psss
      missConSet = Set.difference (nameConSet (dataDefs sig d)) conSet
  {-# COMPILE AGDA2HS existMissCon #-}

  -- The core usefulness checking algorithm in the paper
  {-# TERMINATING #-}
  isUseful : (P : PatternStackMatrix αss) (pss : PatternStack αss) → Bool
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
