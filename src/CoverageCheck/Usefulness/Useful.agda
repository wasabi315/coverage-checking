open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm
open import CoverageCheck.Usefulness.Properties
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

module CoverageCheck.Usefulness.Useful
  ⦃ @0 globals : Globals ⦄
  where

-- agda2hs does not import class methods for some reason, so we need to import them manually
{-# FOREIGN AGDA2HS
import CoverageCheck.Usefulness.Algorithm
#-}

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    αss βss : TyStack
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 αss0 βss0 : TyStack
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  -- ps is useful with respect to P if
  --   1. there is a list of values vs that matches ps
  --   2. vs does not match any row in P
  -- Usefulness can also be used to formulate redundancy
  record Useful (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0) : Type where
    no-eta-equality
    pattern
    constructor MkUseful
    field
      witness       : ValueStack αss0
      @0 P⋠witness  : P ⋠**ˢ witness
      @0 ps≼witness : ps ≼*ˢ witness
  open Useful public
  {-# COMPILE AGDA2HS Useful newtype #-}

private
  pattern ⟪_,_,_⟫ vs nis iss = MkUseful vs nis iss

--------------------------------------------------------------------------------
-- Properties of usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  -- [] is useful wrt []
  usefulNilOkCase : Useful [] []
  usefulNilOkCase = ⟪ [] , (λ ()) , [] ⟫
  {-# COMPILE AGDA2HS usefulNilOkCase #-}

  -- [] is not wrt any non-empty matrix
  usefulNilBadCase : {ps : PatternStack []} {P : PatternMatrixStack []}
    → ¬ Useful (ps ∷ P) []
  usefulNilBadCase {[]} ⟪ [] , h , _ ⟫ = contradiction (here []) h


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ([] ∷ αss0)}
  {@0 pss : PatternStack αss0}
  where

  usefulTailCase : Useful (map tailAll P) pss → Useful P ([] ∷ pss)
  usefulTailCase ⟪ vss , nis , iss ⟫ =
    ⟪ [] ∷ vss
    , contraposition (gmapAny⁺ λ where {[] ∷ pss} (_ ∷ iss') → iss') nis
    , [] ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulTailCase #-}

  usefulTailCaseInv : Useful P ([] ∷ pss) → Useful (map tailAll P) pss
  usefulTailCaseInv ⟪ [] ∷ vss , nis , [] ∷ iss ⟫ =
    ⟪ vss
    , contraposition (gmapAny⁻ λ where {[] ∷ pss} iss' → [] ∷ iss') nis
    , iss ⟫


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
  {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulOrCaseL : Useful P ((r₁ ∷ ps) ∷ pss) → Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseL ⟪ (v ∷ vs) ∷ vss , nis , (i ∷ is) ∷ iss ⟫ =
    ⟪ (v ∷ vs) ∷ vss , nis , (∣≼ˡ i ∷ is) ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseL transparent #-}

  usefulOrCaseR : Useful P ((r₂ ∷ ps) ∷ pss) → Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseR ⟪ (v ∷ vs) ∷ vss , nis , (i ∷ is) ∷ iss ⟫ =
    ⟪ (v ∷ vs) ∷ vss , nis , (∣≼ʳ i ∷ is) ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseR transparent #-}

  usefulOrCase : These (Useful P ((r₁ ∷ ps) ∷ pss)) (Useful P ((r₂ ∷ ps) ∷ pss))
    → Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCase (This h)   = usefulOrCaseL h
  usefulOrCase (That h)   = usefulOrCaseR h
  -- ignore the second argument
  usefulOrCase (Both h _) = usefulOrCaseL h
  {-# COMPILE AGDA2HS usefulOrCase #-}

  @0 usefulOrCaseInv : Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → These (Useful P ((r₁ ∷ ps) ∷ pss)) (Useful P ((r₂ ∷ ps) ∷ pss))
  usefulOrCaseInv ⟪ (v ∷ vs) ∷ vss , nis , (∣≼ˡ i ∷ is) ∷ iss ⟫ =
    This ⟪ (v ∷ vs) ∷ vss , nis , (i ∷ is) ∷ iss ⟫
  usefulOrCaseInv ⟪ (v ∷ vs) ∷ vss , nis , (∣≼ʳ i ∷ is) ∷ iss ⟫ =
    That ⟪ (v ∷ vs) ∷ vss , nis , (i ∷ is) ∷ iss ⟫


module _ ⦃ @0 sig : Signature ⦄ {c : NameCon d0}
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulConCase : Useful (specialize c P) (rs ∷ ps ∷ pss) → Useful P ((con c rs ∷ ps) ∷ pss)
  usefulConCase ⟪ vs' ∷ vs ∷ vss , nis , is' ∷ is ∷ iss ⟫ =
    ⟪ (con c vs' ∷ vs) ∷ vss , contraposition specialize-preserves-≼ nis , (con≼ is' ∷ is) ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulConCase #-}


  usefulConCaseInv : Useful P ((con c rs ∷ ps) ∷ pss) → Useful (specialize c P) (rs ∷ ps ∷ pss)
  usefulConCaseInv ⟪ (con c vs ∷ us) ∷ vss , nis , (con≼ is ∷ is') ∷ iss ⟫ =
    ⟪ vs ∷ us ∷ vss , contraposition specialize-preserves-≼⁻ nis , is ∷ is' ∷ iss ⟫


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- If there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`, `∙ ∷ ps` is also useful wrt P
  usefulWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d0 ] Useful (specialize c P) (—* ∷ ps ∷ pss))
    → Useful P ((— ∷ ps) ∷ pss)
  -- only consider the first constructor
  usefulWildCompCase ((c , ⟪ vs' ∷ vs ∷ vss , nis , _ ∷ is ∷ iss ⟫) ∷ _) =
    ⟪ (con c vs' ∷ vs) ∷ vss , contraposition specialize-preserves-≼ nis , (—≼ ∷ is) ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulWildCompCase #-}

  -- If `∙ ∷ ps` is useful wrt P, there exists a constructor c such that `∙* ++ ps` is useful wrt `specialize c P`
  usefulWildCompCaseInv :
      Useful P ((— ∷ ps) ∷ pss)
    → NonEmpty (Σ[ c ∈ NameCon d0 ] Useful (specialize c P) (—* ∷ ps ∷ pss))
  usefulWildCompCaseInv ⟪ (con c us ∷ vs) ∷ vss , nis , (—≼ ∷ is) ∷ iss ⟫ =
    (c , ⟪ us ∷ vs ∷ vss , contraposition specialize-preserves-≼⁻ nis , —≼* ∷ is ∷ iss ⟫) ∷ []


module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ {d}
  {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- If there is a constructor c that does not appear in the first column of P, and ps is useful wrt default P, ∙ ∷ ps is also useful wrt P.
  usefulWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → Useful (default_ P) (ps ∷ pss) → Useful P ((— ∷ ps) ∷ pss)
  -- only consider inhab
  usefulWildMissCase (Left (Erased h)) ⟪ vs ∷ vss , nis , is ∷ iss ⟫ =
    ⟪ (inhab ∷ vs) ∷ vss , contraposition (default-preserves-≼ (h _)) nis , (—≼ ∷ is) ∷ iss ⟫
  -- only consider the first constructor
  usefulWildMissCase (Right (c ⟨ h ⟩ ∷ _)) ⟪ vs ∷ vss , nis , is ∷ iss ⟫ =
    ⟪ (inhabAt c ∷ vs) ∷ vss , contraposition (default-preserves-≼ h) nis , (—≼ ∷ is) ∷ iss ⟫
  {-# COMPILE AGDA2HS usefulWildMissCase #-}

  -- ps is useful wrt (default P) if (∙ ∷ ps) is useful wrt P
  usefulWildMissCaseInv : Useful P ((— ∷ ps) ∷ pss) → Useful (default_ P) (ps ∷ pss)
  usefulWildMissCaseInv ⟪ (v ∷ vs) ∷ vss , nis , (—≼ ∷ is) ∷ iss ⟫ =
    ⟪ vs ∷ vss , contraposition default-preserves-≼⁻ nis , is ∷ iss ⟫

--------------------------------------------------------------------------------

instance iUsefulnessUseful : Usefulness Useful
iUsefulnessUseful .nilOkCase       = usefulNilOkCase
iUsefulnessUseful .nilBadCase      = usefulNilBadCase
iUsefulnessUseful .tailCase        = usefulTailCase
iUsefulnessUseful .tailCaseInv     = usefulTailCaseInv
iUsefulnessUseful .orCase          = usefulOrCase
iUsefulnessUseful .orCaseInv       = usefulOrCaseInv
iUsefulnessUseful .conCase         = usefulConCase
iUsefulnessUseful .conCaseInv      = usefulConCaseInv
iUsefulnessUseful .wildMissCase    = usefulWildMissCase
iUsefulnessUseful .wildMissCaseInv = λ _ → usefulWildMissCaseInv
iUsefulnessUseful .wildCompCase    = λ _ → usefulWildCompCase
iUsefulnessUseful .wildCompCaseInv = λ _ → usefulWildCompCaseInv
{-# COMPILE AGDA2HS iUsefulnessUseful #-}
