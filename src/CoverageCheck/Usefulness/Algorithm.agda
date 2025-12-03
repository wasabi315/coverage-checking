open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

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
-- Properties of usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  usefulNilOkCase : UsefulS [] []
  usefulNilOkCase = ⟪ [] , (λ ()) , [] ⟫ ∷ []
  {-# COMPILE AGDA2HS usefulNilOkCase #-}

  usefulNilBadCase : ∀ {ps P} → ¬ UsefulS (ps ∷ P) []
  usefulNilBadCase {ps = []} (⟪ [] , h , _ ⟫ ∷ _) =
    contradiction [] (h (here []))


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternStackMatrix ([] ∷ αss0)} {@0 pss : PatternStack αss0}
  where

  usefulTailCase' : UsefulS' (map tailAll P) pss → UsefulS' P ([] ∷ pss)
  usefulTailCase' ⟪ qss , disj , sss ⟫ =
    ⟪ [] ∷ qss , #-tail⁻ disj , [] ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulTailCase' #-}

  usefulTailCase : UsefulS (map tailAll P) pss → UsefulS P ([] ∷ pss)
  usefulTailCase = fmap usefulTailCase'
  {-# COMPILE AGDA2HS usefulTailCase inline #-}

  usefulTailCaseInv' : UsefulS' P ([] ∷ pss) → UsefulS' (map tailAll P) pss
  usefulTailCaseInv' ⟪ [] ∷ qss , disj , [] ∷ sss ⟫ =
    ⟪ qss , #-tail disj , sss ⟫

  usefulTailCaseInv : UsefulS P ([] ∷ pss) → UsefulS (map tailAll P) pss
  usefulTailCaseInv = fmap usefulTailCaseInv'


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternStackMatrix ((α0 ∷ αs0) ∷ αss0)}
  {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulOrCaseL'
    : UsefulS' P ((r₁ ∷ ps) ∷ pss)
    → UsefulS' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseL' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseL' transparent #-}

  usefulOrCaseList
    : List (UsefulS' P ((r₁ ∷ ps) ∷ pss))
    → List (UsefulS' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseList []       = []
  usefulOrCaseList (h ∷ hs) = usefulOrCaseL' h ∷ usefulOrCaseList hs
  {-# COMPILE AGDA2HS usefulOrCaseList transparent #-}

  usefulOrCaseL
    : UsefulS P ((r₁ ∷ ps) ∷ pss)
    → UsefulS P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseL (h ∷ hs) = usefulOrCaseL' h ∷ usefulOrCaseList hs
  {-# COMPILE AGDA2HS usefulOrCaseL transparent #-}

  usefulOrCaseR'
    : UsefulS' P ((r₂ ∷ ps) ∷ pss)
    → UsefulS' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseR' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseR' transparent #-}

  usefulOrCaseRList
    : List (UsefulS' P ((r₂ ∷ ps) ∷ pss))
    → List (UsefulS' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseRList []       = []
  usefulOrCaseRList (h ∷ hs) = usefulOrCaseR' h ∷ usefulOrCaseRList hs
  {-# COMPILE AGDA2HS usefulOrCaseRList transparent #-}

  usefulOrCaseR
    : UsefulS P ((r₂ ∷ ps) ∷ pss)
    → UsefulS P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseR (h ∷ hs) = usefulOrCaseR' h ∷ usefulOrCaseRList hs
  {-# COMPILE AGDA2HS usefulOrCaseR transparent #-}

  usefulOrCase
    : These (UsefulS P ((r₁ ∷ ps) ∷ pss)) (UsefulS P ((r₂ ∷ ps) ∷ pss))
    → UsefulS P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCase (This hs) = usefulOrCaseL hs
  usefulOrCase (That hs) = usefulOrCaseR hs
  usefulOrCase (Both hs1 hs2) = usefulOrCaseL hs1 <> usefulOrCaseR hs2
  {-# COMPILE AGDA2HS usefulOrCase #-}

  @0 usefulOrCaseInv'
    : UsefulS' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → Either (UsefulS' P ((r₁ ∷ ps) ∷ pss)) (UsefulS' P ((r₂ ∷ ps) ∷ pss))
  usefulOrCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫ =
    Left (⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫)
  usefulOrCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫ =
    Right (⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫)

  @0 usefulOrCaseInv
    : UsefulS P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → These (UsefulS P ((r₁ ∷ ps) ∷ pss)) (UsefulS P ((r₂ ∷ ps) ∷ pss))
  usefulOrCaseInv = partitionEithersNonEmpty ∘ fmap usefulOrCaseInv'


module _ ⦃ @0 sig : Signature ⦄ {c : NameCon d0}
  {@0 P : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 rs : Patterns (argsTy (dataDefs sig d0) c)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulConCase' :
      UsefulS' (specialize c P) (rs ∷ ps ∷ pss)
    → UsefulS' P ((con c rs ∷ ps) ∷ pss)
  usefulConCase' ⟪ qs' ∷ qs ∷ qss , disj , ss' ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , specialize-preserves-#⁻ disj
    , (con⊆ ss' ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulConCase' #-}

  usefulConCase
    : UsefulS (specialize c P) (rs ∷ ps ∷ pss)
    → UsefulS P ((con c rs ∷ ps) ∷ pss)
  usefulConCase = fmap usefulConCase'
  {-# COMPILE AGDA2HS usefulConCase inline #-}

  usefulConCaseInv' :
      UsefulS' P ((con c rs ∷ ps) ∷ pss)
    → UsefulS' (specialize c P) (rs ∷ ps ∷ pss)
  usefulConCaseInv' ⟪ (con c qs' ∷ qs) ∷ qss , disj , (con⊆ ss' ∷ ss) ∷ sss ⟫ =
    ⟪ qs' ∷ qs ∷ qss
    , specialize-preserves-# disj
    , ss' ∷ ss ∷ sss ⟫

  usefulConCaseInv
    : UsefulS P ((con c rs ∷ ps) ∷ pss)
    → UsefulS (specialize c P) (rs ∷ ps ∷ pss)
  usefulConCaseInv = fmap usefulConCaseInv'


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulWildCompCase' : (c : NameCon d0)
    → UsefulS' (specialize c P) (—* ∷ ps ∷ pss)
    → UsefulS' P ((— ∷ ps) ∷ pss)
  usefulWildCompCase' c ⟪ qs' ∷ qs ∷ qss , disj , _ ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , specialize-preserves-#⁻ disj
    , (—⊆ ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulWildCompCase' #-}

  usefulWildCompCase
    : NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulS (specialize c P) (—* ∷ ps ∷ pss))
    → UsefulS P ((— ∷ ps) ∷ pss)
  usefulWildCompCase hs = do
    c , hs' ← hs
    fmap (usefulWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulWildCompCase #-}


module _ ⦃ @0 sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  {@0 P : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  @0 usefulWildCompCaseInv' : ∀ qss
    → P #ˢᵐ qss
    → ((— ∷ ps) ∷ pss) ⊆ˢ qss
    → Σ[ c ∈ NameCon d0 ] UsefulS' (specialize c P) (—* ∷ ps ∷ pss)
  usefulWildCompCaseInv' ((— ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    exampleCon ,
    ⟪ —* ∷ qs ∷ qss , specialize-preserves-#-wild disj , —⊆* ∷ ss ∷ sss ⟫
  usefulWildCompCaseInv' ((con c qs' ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    c ,
    ⟪ qs' ∷ qs ∷ qss , specialize-preserves-# disj , —⊆* ∷ ss ∷ sss ⟫
  usefulWildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) disj ((s ∷ ss) ∷ sss) =
    usefulWildCompCaseInv' ((q₁ ∷ qs) ∷ qss) (#-∣ˡ disj) ((—⊆ ∷ ss) ∷ sss)

  @0 usefulWildCompCaseInv
    : UsefulS P ((— ∷ ps) ∷ pss)
    → NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulS (specialize c P) (—* ∷ ps ∷ pss))
  usefulWildCompCaseInv hs = do
    ⟪ qss , disj , sss ⟫ ← hs
    let c , h' = usefulWildCompCaseInv' qss disj sss
    pure (c , h' ∷ [])


module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ {d}
  {@0 P : PatternStackMatrix ((TyData d ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulWildMissCase'
    : Either (Erase (∀ c → c ∉ˢᵐ P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉ˢᵐ P))
    → UsefulS' (default_ P) (ps ∷ pss)
    → UsefulS P ((— ∷ ps) ∷ pss)
  usefulWildMissCase' (Left (Erased h)) ⟪ qs ∷ qss , disj , ss ∷ sss ⟫ =
    ⟪ (— ∷ qs) ∷ qss
    , default-preserves-#⁻-wild h disj
    , (—⊆ ∷ ss) ∷ sss ⟫ ∷ []
  usefulWildMissCase' (Right hs) ⟪ qs ∷ qss , disj , ss ∷ sss ⟫ =
    fmap
      (λ where
        (c ⟨ h ⟩) →
          ⟪ (con c —* ∷ qs) ∷ qss
          , default-preserves-#⁻ h disj
          , (—⊆ ∷ ss) ∷ sss ⟫)
      hs
  {-# COMPILE AGDA2HS usefulWildMissCase' #-}

  usefulWildMissCase
    : Either (Erase (∀ c → c ∉ˢᵐ P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉ˢᵐ P))
    → UsefulS (default_ P) (ps ∷ pss)
    → UsefulS P ((— ∷ ps) ∷ pss)
  usefulWildMissCase h hs = hs >>= usefulWildMissCase' h
  {-# COMPILE AGDA2HS usefulWildMissCase #-}

  usefulWildMissCaseInv'
    : UsefulS' P ((— ∷ ps) ∷ pss)
    → UsefulS' (default_ P) (ps ∷ pss)
  usefulWildMissCaseInv' ⟪ (q ∷ qs) ∷ qss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ qs ∷ qss , default-preserves-# disj , ss ∷ sss ⟫

  usefulWildMissCaseInv
    : UsefulS P ((— ∷ ps) ∷ pss)
    → UsefulS (default_ P) (ps ∷ pss)
  usefulWildMissCaseInv = fmap usefulWildMissCaseInv'

module _
  ⦃ sig : Signature ⦄
  ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful' : (P : PatternStackMatrix αss) (ps : PatternStack αss)
    → @0 UsefulAcc P ps
    → DecP (UsefulS P ps)
  decUseful' {[]} []      [] done = Yes usefulNilOkCase
  decUseful' {[]} (_ ∷ _) [] done = No usefulNilBadCase
  decUseful' {[] ∷ αss} psss ([] ∷ pss) (tailStep h) =
    mapDecP usefulTailCase usefulTailCaseInv
      (decUseful' (map tailAll psss) pss h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((— ∷ ps) ∷ pss) (wildStep h h') =
    case decExistMissCon psss of λ where
      (Right miss) →
        mapDecP (usefulWildMissCase miss) usefulWildMissCaseInv
          (decUseful' (default_ psss) (ps ∷ pss) h)
      (Left (Erased comp)) →
        mapDecP usefulWildCompCase usefulWildCompCaseInv
          (decPAnyNameCon (dataDefs sig d) λ c →
            decUseful' (specialize c psss) (—* ∷ ps ∷ pss) (h' c (comp c)))
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((con c rs ∷ ps) ∷ pss) (conStep h) =
    mapDecP usefulConCase usefulConCaseInv
      (decUseful' (specialize c psss) (rs ∷ ps ∷ pss) h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((r₁ ∣ r₂ ∷ ps) ∷ pss) (orStep h h') =
    mapDecP usefulOrCase usefulOrCaseInv
      (theseDecP (decUseful' psss ((r₁ ∷ ps) ∷ pss) h) (decUseful' psss ((r₂ ∷ ps) ∷ pss) h'))
  {-# COMPILE AGDA2HS decUseful' #-}

  decUseful : (pss : PatternMatrix αs) (ps : Patterns αs)
    → DecP (Useful pss ps)
  decUseful pss ps =
    mapDecP UsefulS→Useful Useful→UsefulS
      (decUseful' (map (_∷ []) pss) (ps ∷ []) (∀UsefulAcc _ _))
  {-# COMPILE AGDA2HS decUseful #-}
