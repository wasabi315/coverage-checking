open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_)

open import CoverageCheck.Usefulness.Definition
open import CoverageCheck.Usefulness.Algorithm.Types
open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors
open import CoverageCheck.Usefulness.Algorithm.Properties
open import CoverageCheck.Usefulness.Algorithm.Termination

module CoverageCheck.Usefulness.Algorithm
  ⦃ @0 globals : Globals ⦄
  where

{-# FOREIGN AGDA2HS
import CoverageCheck.Usefulness.Definition (Useful(..))
#-}

private open module @0 G = Globals globals

private
  variable
    αs : Tys
    αss : TyStack
    @0 α0 : Ty
    @0 αs0 : Tys
    @0 αss0 : TyStack
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Usefulness problem reduced to a set of smaller sub-problems equivalent to the original problem

module _ ⦃ @0 sig : Signature ⦄ where

  -- The smallest usefulness problem

  nilOkCase : UsefulS [] []
  nilOkCase = ⟪ [] , (λ ()) , [] ⟫ ∷ []
  {-# COMPILE AGDA2HS nilOkCase #-}

  nilBadCase : ∀ {ps P} → ¬ UsefulS (ps ∷ P) []
  nilBadCase {ps = []} (⟪ [] , h , _ ⟫ ∷ _) =
    contradiction [] (h (here []))


module _ ⦃ @0 sig : Signature ⦄
  {@0 psmat : PatternStackMatrix ([] ∷ αss0)} {@0 pss : PatternStack αss0}
  where

  -- Case for tailing a pattern stack

  tailCase' : UsefulS' (map tailAll psmat) pss → UsefulS' psmat ([] ∷ pss)
  tailCase' ⟪ qss , disj , sss ⟫ =
    ⟪ [] ∷ qss , #-tail⁻ disj , [] ∷ sss ⟫
  {-# COMPILE AGDA2HS tailCase' #-}

  tailCase : UsefulS (map tailAll psmat) pss → UsefulS psmat ([] ∷ pss)
  tailCase = fmap tailCase'
  {-# COMPILE AGDA2HS tailCase inline #-}

  tailCaseInv' : UsefulS' psmat ([] ∷ pss) → UsefulS' (map tailAll psmat) pss
  tailCaseInv' ⟪ [] ∷ qss , disj , [] ∷ sss ⟫ =
    ⟪ qss , #-tail disj , sss ⟫

  tailCaseInv : UsefulS psmat ([] ∷ pss) → UsefulS (map tailAll psmat) pss
  tailCaseInv = fmap tailCaseInv'


module _ ⦃ @0 sig : Signature ⦄
  {@0 psmat : PatternStackMatrix ((α0 ∷ αs0) ∷ αss0)}
  {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- Case for or-patterns

  orCaseL'
    : UsefulS' psmat ((r₁ ∷ ps) ∷ pss)
    → UsefulS' psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  orCaseL' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS orCaseL' transparent #-}

  orCaseList
    : List (UsefulS' psmat ((r₁ ∷ ps) ∷ pss))
    → List (UsefulS' psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  orCaseList []       = []
  orCaseList (h ∷ hs) = orCaseL' h ∷ orCaseList hs
  {-# COMPILE AGDA2HS orCaseList transparent #-}

  orCaseL
    : UsefulS psmat ((r₁ ∷ ps) ∷ pss)
    → UsefulS psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  orCaseL (h ∷ hs) = orCaseL' h ∷ orCaseList hs
  {-# COMPILE AGDA2HS orCaseL transparent #-}

  orCaseR'
    : UsefulS' psmat ((r₂ ∷ ps) ∷ pss)
    → UsefulS' psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  orCaseR' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS orCaseR' transparent #-}

  orCaseRList
    : List (UsefulS' psmat ((r₂ ∷ ps) ∷ pss))
    → List (UsefulS' psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  orCaseRList []       = []
  orCaseRList (h ∷ hs) = orCaseR' h ∷ orCaseRList hs
  {-# COMPILE AGDA2HS orCaseRList transparent #-}

  orCaseR
    : UsefulS psmat ((r₂ ∷ ps) ∷ pss)
    → UsefulS psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  orCaseR (h ∷ hs) = orCaseR' h ∷ orCaseRList hs
  {-# COMPILE AGDA2HS orCaseR transparent #-}

  orCase
    : These (UsefulS psmat ((r₁ ∷ ps) ∷ pss)) (UsefulS psmat ((r₂ ∷ ps) ∷ pss))
    → UsefulS psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  orCase (This hs) = orCaseL hs
  orCase (That hs) = orCaseR hs
  orCase (Both hs1 hs2) = orCaseL hs1 <> orCaseR hs2
  {-# COMPILE AGDA2HS orCase #-}

  @0 orCaseInv'
    : UsefulS' psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → Either (UsefulS' psmat ((r₁ ∷ ps) ∷ pss)) (UsefulS' psmat ((r₂ ∷ ps) ∷ pss))
  orCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫ =
    Left ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫
  orCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫ =
    Right ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫

  @0 orCaseInv
    : UsefulS psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → These (UsefulS psmat ((r₁ ∷ ps) ∷ pss)) (UsefulS psmat ((r₂ ∷ ps) ∷ pss))
  orCaseInv = partitionEithersNonEmpty ∘ fmap orCaseInv'


module _ ⦃ @0 sig : Signature ⦄ {c : NameCon d0}
  {@0 psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 rs : Patterns (argsTy (dataDefs sig d0) c)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- Case for constructor patterns

  conCase'
    : UsefulS' (specialize c psmat) (rs ∷ ps ∷ pss)
    → UsefulS' psmat ((con c rs ∷ ps) ∷ pss)
  conCase' ⟪ qs' ∷ qs ∷ qss , disj , ss' ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , specialize-preserves-#⁻ disj
    , (con⊆ ss' ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS conCase' #-}

  conCase
    : UsefulS (specialize c psmat) (rs ∷ ps ∷ pss)
    → UsefulS psmat ((con c rs ∷ ps) ∷ pss)
  conCase = fmap conCase'
  {-# COMPILE AGDA2HS conCase inline #-}

  conCaseInv'
    : UsefulS' psmat ((con c rs ∷ ps) ∷ pss)
    → UsefulS' (specialize c psmat) (rs ∷ ps ∷ pss)
  conCaseInv' ⟪ (con c qs' ∷ qs) ∷ qss , disj , (con⊆ ss' ∷ ss) ∷ sss ⟫ =
    ⟪ qs' ∷ qs ∷ qss
    , specialize-preserves-# disj
    , ss' ∷ ss ∷ sss ⟫

  conCaseInv
    : UsefulS psmat ((con c rs ∷ ps) ∷ pss)
    → UsefulS (specialize c psmat) (rs ∷ ps ∷ pss)
  conCaseInv = fmap conCaseInv'


module _ ⦃ @0 sig : Signature ⦄
  {@0 psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- Case for wildcard patterns (forward direction)

  wildCompCase' : (c : NameCon d0)
    → UsefulS' (specialize c psmat) (—* ∷ ps ∷ pss)
    → UsefulS' psmat ((— ∷ ps) ∷ pss)
  wildCompCase' c ⟪ qs' ∷ qs ∷ qss , disj , _ ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , specialize-preserves-#⁻ disj
    , (—⊆ ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS wildCompCase' #-}

  wildCompCase
    : NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulS (specialize c psmat) (—* ∷ ps ∷ pss))
    → UsefulS psmat ((— ∷ ps) ∷ pss)
  wildCompCase hs = do
    c , hs' ← hs
    fmap (wildCompCase' c) hs'
  {-# COMPILE AGDA2HS wildCompCase #-}


module _ ⦃ @0 sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  {@0 psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- Case for wildcard patterns (backward direction)
  -- Requires the non-empty axiom

  @0 wildCompCaseInv' : ∀ qss
    → psmat #ˢᵐ qss
    → ((— ∷ ps) ∷ pss) ⊆ˢ qss
    → Σ[ c ∈ NameCon d0 ] UsefulS' (specialize c psmat) (—* ∷ ps ∷ pss)
  wildCompCaseInv' ((— ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    exampleCon ,
    ⟪ —* ∷ qs ∷ qss , specialize-preserves-#-wild disj , —⊆* ∷ ss ∷ sss ⟫
  wildCompCaseInv' ((con c qs' ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    c ,
    ⟪ qs' ∷ qs ∷ qss , specialize-preserves-# disj , —⊆* ∷ ss ∷ sss ⟫
  wildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    wildCompCaseInv' ((q₁ ∷ qs) ∷ qss) (#-∣ˡ disj) ((—⊆ ∷ ss) ∷ sss)

  @0 wildCompCaseInv
    : UsefulS psmat ((— ∷ ps) ∷ pss)
    → NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulS (specialize c psmat) (—* ∷ ps ∷ pss))
  wildCompCaseInv hs = do
    ⟪ qss , disj , sss ⟫ ← hs
    let c , h' = wildCompCaseInv' qss disj sss
    pure (c , h' ∷ [])


module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ {d}
  {@0 psmat : PatternStackMatrix ((TyData d ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  -- Case for wildcard patterns (missing constructor case)
  -- Requires the non-empty axiom

  wildMissCase'
    : Either
        (Erase (∀ c → c ∉ˢᵐ psmat))
        (NonEmpty (∃[ c ∈ NameCon d ] c ∉ˢᵐ psmat))
    → UsefulS' (default_ psmat) (ps ∷ pss)
    → UsefulS psmat ((— ∷ ps) ∷ pss)
  wildMissCase' (Left (Erased h)) ⟪ qs ∷ qss , disj , ss ∷ sss ⟫ =
    ⟪ (— ∷ qs) ∷ qss
    , default-preserves-#⁻-wild h disj
    , (—⊆ ∷ ss) ∷ sss ⟫ ∷ []
  wildMissCase' (Right hs) ⟪ qs ∷ qss , disj , ss ∷ sss ⟫ =
    fmap
      (λ where
        (c ⟨ h ⟩) →
          ⟪ (con c —* ∷ qs) ∷ qss
          , default-preserves-#⁻ h disj
          , (—⊆ ∷ ss) ∷ sss ⟫)
      hs
  {-# COMPILE AGDA2HS wildMissCase' #-}

  wildMissCase
    : Either
        (Erase (∀ c → c ∉ˢᵐ psmat))
        (NonEmpty (∃[ c ∈ NameCon d ] c ∉ˢᵐ psmat))
    → UsefulS (default_ psmat) (ps ∷ pss)
    → UsefulS psmat ((— ∷ ps) ∷ pss)
  wildMissCase h hs = hs >>= wildMissCase' h
  {-# COMPILE AGDA2HS wildMissCase #-}

  wildMissCaseInv'
    : UsefulS' psmat ((— ∷ ps) ∷ pss)
    → UsefulS' (default_ psmat) (ps ∷ pss)
  wildMissCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ qs ∷ qss , default-preserves-# disj , ss ∷ sss ⟫

  wildMissCaseInv
    : UsefulS psmat ((— ∷ ps) ∷ pss)
    → UsefulS (default_ psmat) (ps ∷ pss)
  wildMissCaseInv = fmap wildMissCaseInv'

--------------------------------------------------------------------------------
-- The main function: an evidence-producing version of isUseful
-- Computes patterns that witness usefulness, instead of just returning a boolean
-- Useful for informative error reporting

module _
  ⦃ sig : Signature ⦄
  ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decPUseful' : (psmat : PatternStackMatrix αss) (ps : PatternStack αss)
    → @0 UsefulAcc psmat ps
    → DecP (UsefulS psmat ps)
  decPUseful' {[]} [] [] done = Yes nilOkCase
  decPUseful' {[]} (_ ∷ _) [] done = No nilBadCase
  decPUseful' {[] ∷ αss} psmat ([] ∷ pss) (tailStep h) =
    mapDecP tailCase tailCaseInv
      (decPUseful' (map tailAll psmat) pss h)
  decPUseful' {(TyData d ∷ αs) ∷ αss} psmat ((— ∷ ps) ∷ pss) (wildStep h h') =
    case decExistMissCon psmat of λ where
      (Right miss) →
        mapDecP (wildMissCase miss) wildMissCaseInv
          (decPUseful' (default_ psmat) (ps ∷ pss) h)
      (Left (Erased comp)) →
        mapDecP wildCompCase wildCompCaseInv
          (decPAnyNameCon (dataDefs sig d) λ c →
            decPUseful' (specialize c psmat) (—* ∷ ps ∷ pss) (h' c (comp c)))
  decPUseful' {(TyData d ∷ αs) ∷ αss} psmat ((con c rs ∷ ps) ∷ pss) (conStep h) =
    mapDecP conCase conCaseInv
      (decPUseful' (specialize c psmat) (rs ∷ ps ∷ pss) h)
  decPUseful' {(TyData d ∷ αs) ∷ αss} psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss) (orStep h h') =
    mapDecP orCase orCaseInv
      (theseDecP
        (decPUseful' psmat ((r₁ ∷ ps) ∷ pss) h)
        (decPUseful' psmat ((r₂ ∷ ps) ∷ pss) h'))
  {-# COMPILE AGDA2HS decPUseful' #-}

  decPUseful : (pmat : PatternMatrix αs) (ps : Patterns αs)
    → DecP (Useful pmat ps)
  decPUseful pmat ps =
    mapDecP UsefulS→Useful Useful→UsefulS
      (decPUseful' (map (_∷ []) pmat) (ps ∷ []) (∀UsefulAcc _ _))
  {-# COMPILE AGDA2HS decPUseful #-}

-- Evidence-producing on Agda side, but boolean-returning on Haskell side

module _
  ⦃ sig : Signature ⦄
  ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful' : (psmat : PatternStackMatrix αss) (ps : PatternStack αss)
    → @0 UsefulAcc psmat ps
    → Dec (UsefulS psmat ps)
  decUseful' {[]} [] [] done = True ⟨ nilOkCase ⟩
  decUseful' {[]} (_ ∷ _) [] done = False ⟨ nilBadCase ⟩
  decUseful' {[] ∷ αss} psmat ([] ∷ pss) (tailStep h) =
    mapDec tailCase tailCaseInv
      (decUseful' (map tailAll psmat) pss h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psmat ((— ∷ ps) ∷ pss) (wildStep h h') =
    case decExistMissCon psmat of λ where
      (Right miss) →
        mapDec (wildMissCase miss) wildMissCaseInv
          (decUseful' (default_ psmat) (ps ∷ pss) h)
      (Left (Erased comp)) →
        mapDec wildCompCase wildCompCaseInv
          (decAnyNameCon (dataDefs sig d) λ c →
            decUseful' (specialize c psmat) (—* ∷ ps ∷ pss) (h' c (comp c)))
  decUseful' {(TyData d ∷ αs) ∷ αss} psmat ((con c rs ∷ ps) ∷ pss) (conStep h) =
    mapDec conCase conCaseInv
      (decUseful' (specialize c psmat) (rs ∷ ps ∷ pss) h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psmat ((r₁ ∣ r₂ ∷ ps) ∷ pss) (orStep h h') =
    mapDec
      (either orCaseL orCaseR)
      (bimap NonEmpty.singleton NonEmpty.singleton ∘ orCaseInv' ∘ NonEmpty.head)
      (eitherDec
        (decUseful' psmat ((r₁ ∷ ps) ∷ pss) h)
        (decUseful' psmat ((r₂ ∷ ps) ∷ pss) h'))
  {-# COMPILE AGDA2HS decUseful' #-}

  decUseful : (pmat : PatternMatrix αs) (ps : Patterns αs)
    → Dec (Useful pmat ps)
  decUseful pmat ps =
    mapDec UsefulS→Useful Useful→UsefulS
      (decUseful' (map (_∷ []) pmat) (ps ∷ []) (∀UsefulAcc _ _))
  {-# COMPILE AGDA2HS decUseful #-}
