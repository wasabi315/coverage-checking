open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_)

open import CoverageCheck.Usefulness.Algorithm.Raw
open import CoverageCheck.Usefulness.Algorithm.MissingConstructors
open import CoverageCheck.Usefulness.Algorithm.Properties
open import CoverageCheck.Usefulness.Definition
open import CoverageCheck.Usefulness.Algorithm.Termination

module CoverageCheck.Usefulness.Algorithm
  ⦃ @0 globals : Globals ⦄
  where

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
-- Properties of usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  usefulNilOkCase : Useful [] []
  usefulNilOkCase = MkUseful (⟪ [] , [] , (λ ()) , [] ⟫ ∷ [])
  {-# COMPILE AGDA2HS usefulNilOkCase #-}

  usefulNilBadCase : {ps : PatternStack []} {P : PatternMatrixStack []} → ¬ Useful (ps ∷ P) []
  usefulNilBadCase {ps = []} (MkUseful (⟪ [] , _ , h , _ ⟫ ∷ _)) =
    contradiction [] (h (here []))


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ([] ∷ αss0)} {@0 pss : PatternStack αss0}
  where

  usefulTailCase' : Useful' (map tailAll P) pss → Useful' P ([] ∷ pss)
  usefulTailCase' ⟪ qss , iss , disj , sss ⟫ =
    ⟪ [] ∷ qss , [] ∷ iss , #**-tail⁻ disj , [] ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulTailCase' #-}

  usefulTailCase : Useful (map tailAll P) pss → Useful P ([] ∷ pss)
  usefulTailCase (MkUseful hs) = MkUseful (fmap usefulTailCase' hs)
  {-# COMPILE AGDA2HS usefulTailCase #-}

  usefulTailCaseInv' : Useful' P ([] ∷ pss) → Useful' (map tailAll P) pss
  usefulTailCaseInv' ⟪ [] ∷ qss , [] ∷ iss , disj , [] ∷ sss ⟫ =
    ⟪ qss , iss , #**-tail disj , sss ⟫

  usefulTailCaseInv : Useful P ([] ∷ pss) → Useful (map tailAll P) pss
  usefulTailCaseInv (MkUseful hs) = MkUseful (fmap usefulTailCaseInv' hs)


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
  {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulOrCaseL' : Useful' P ((r₁ ∷ ps) ∷ pss) → Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseL' ⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseL' transparent #-}

  usefulOrCaseList : List (Useful' P ((r₁ ∷ ps) ∷ pss)) → List (Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseList []       = []
  usefulOrCaseList (h ∷ hs) = usefulOrCaseL' h ∷ usefulOrCaseList hs
  {-# COMPILE AGDA2HS usefulOrCaseList transparent #-}

  usefulOrCaseL : NonEmpty (Useful' P ((r₁ ∷ ps) ∷ pss)) → NonEmpty (Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseL (h ∷ hs) = usefulOrCaseL' h ∷ usefulOrCaseList hs
  {-# COMPILE AGDA2HS usefulOrCaseL transparent #-}

  usefulOrCaseR' : Useful' P ((r₂ ∷ ps) ∷ pss) → Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCaseR' ⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulOrCaseR' transparent #-}

  usefulOrCaseRList : List (Useful' P ((r₂ ∷ ps) ∷ pss)) → List (Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseRList []       = []
  usefulOrCaseRList (h ∷ hs) = usefulOrCaseR' h ∷ usefulOrCaseRList hs
  {-# COMPILE AGDA2HS usefulOrCaseRList transparent #-}

  usefulOrCaseR : NonEmpty (Useful' P ((r₂ ∷ ps) ∷ pss)) → NonEmpty (Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulOrCaseR (h ∷ hs) = usefulOrCaseR' h ∷ usefulOrCaseRList hs
  {-# COMPILE AGDA2HS usefulOrCaseR transparent #-}

  usefulOrCase :
      These (Useful P ((r₁ ∷ ps) ∷ pss)) (Useful P ((r₂ ∷ ps) ∷ pss))
    → Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulOrCase (This (MkUseful hs)) = MkUseful (usefulOrCaseL hs)
  usefulOrCase (That (MkUseful hs)) = MkUseful (usefulOrCaseR hs)
  usefulOrCase (Both (MkUseful hs) (MkUseful hs')) = MkUseful (usefulOrCaseL hs <> usefulOrCaseR hs')
  {-# COMPILE AGDA2HS usefulOrCase #-}

  @0 usefulOrCaseInv' :
      Useful' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → Either (Useful' P ((r₁ ∷ ps) ∷ pss)) (Useful' P ((r₂ ∷ ps) ∷ pss))
  usefulOrCaseInv' ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫ =
    Left (⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫)
  usefulOrCaseInv' ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫ =
    Right (⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫)

  @0 usefulOrCaseInv :
      Useful P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → These (Useful P ((r₁ ∷ ps) ∷ pss)) (Useful P ((r₂ ∷ ps) ∷ pss))
  usefulOrCaseInv (MkUseful hs) = mapThese MkUseful MkUseful
    (partitionEithersNonEmpty (fmap usefulOrCaseInv' hs))


module _ ⦃ @0 sig : Signature ⦄ {c : NameCon d0}
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulConCase' :
      Useful' (specialize c P) (rs ∷ ps ∷ pss)
    → Useful' P ((con c rs ∷ ps) ∷ pss)
  usefulConCase' ⟪ qs' ∷ qs ∷ qss , is' ∷ is ∷ iss , disj , ss' ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , (con≼ is' ∷ is) ∷ iss
    , specialize-preserves-#**⁻ disj
    , (con⊆ ss' ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulConCase' #-}

  usefulConCase :
      Useful (specialize c P) (rs ∷ ps ∷ pss)
    → Useful P ((con c rs ∷ ps) ∷ pss)
  usefulConCase (MkUseful hs) = MkUseful (fmap usefulConCase' hs)
  {-# COMPILE AGDA2HS usefulConCase #-}

  usefulConCaseInv' :
      Useful' P ((con c rs ∷ ps) ∷ pss)
    → Useful' (specialize c P) (rs ∷ ps ∷ pss)
  usefulConCaseInv' ⟪ (con c qs' ∷ qs) ∷ qss , (con≼ is' ∷ is) ∷ iss , disj , (con⊆ ss' ∷ ss) ∷ sss ⟫ =
    ⟪ qs' ∷ qs ∷ qss
    , is' ∷ is ∷ iss
    , specialize-preserves-#** disj
    , ss' ∷ ss ∷ sss ⟫

  usefulConCaseInv :
      Useful P ((con c rs ∷ ps) ∷ pss)
    → Useful (specialize c P) (rs ∷ ps ∷ pss)
  usefulConCaseInv (MkUseful hs) = MkUseful (fmap usefulConCaseInv' hs)


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulWildCompCase' : (c : NameCon d0)
    → Useful' (specialize c P) (—* ∷ ps ∷ pss)
    → Useful' P ((— ∷ ps) ∷ pss)
  usefulWildCompCase' c ⟪ qs' ∷ qs ∷ qss , is' ∷ is ∷ iss , disj , _ ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , (con≼ is' ∷ is) ∷ iss
    , specialize-preserves-#**⁻ disj
    , (—⊆ ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulWildCompCase' #-}

  usefulWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d0 ] Useful (specialize c P) (—* ∷ ps ∷ pss))
    → Useful P ((— ∷ ps) ∷ pss)
  usefulWildCompCase hs = MkUseful do
    c , MkUseful hs' ← hs
    fmap (usefulWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulWildCompCase #-}

  @0 usefulWildCompCaseInv' : ∀ qss {vss}
    → qss ≼*ˢ vss
    → P #** qss
    → ((— ∷ ps) ∷ pss) ⊆*ˢ qss
    → Σ[ c ∈ NameCon d0 ] Useful' (specialize c P) (—* ∷ ps ∷ pss)
  usefulWildCompCaseInv' ((— ∷ qs) ∷ qss) {(con c vs' ∷ vs) ∷ vss} ((i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    c , ⟪ —* ∷ qs ∷ qss
        , iWilds {vs = vs'} ∷ is ∷ iss
        , specialize-preserves-#**-wild disj
        , —⊆* ∷ ss ∷ sss ⟫
  usefulWildCompCaseInv' ((con c qs' ∷ qs) ∷ qss) ((con≼ is' ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    c , ⟪ qs' ∷ qs ∷ qss
        , is' ∷ is ∷ iss
        , specialize-preserves-#** disj
        , —⊆* ∷ ss ∷ sss ⟫
  usefulWildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) ((∣≼ˡ i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    usefulWildCompCaseInv' ((q₁ ∷ qs) ∷ qss) ((i ∷ is) ∷ iss) (#-∣ˡ disj) ((—⊆ ∷ ss) ∷ sss)
  usefulWildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) ((∣≼ʳ i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    usefulWildCompCaseInv' ((q₂ ∷ qs) ∷ qss) ((i ∷ is) ∷ iss) (#-∣ʳ disj) ((—⊆ ∷ ss) ∷ sss)

  @0 usefulWildCompCaseInv :
      Useful P ((— ∷ ps) ∷ pss)
    → NonEmpty (Σ[ c ∈ NameCon d0 ] Useful (specialize c P) (—* ∷ ps ∷ pss))
  usefulWildCompCaseInv (MkUseful hs) = do
    ⟪ qss , iss , disj , sss ⟫ ← hs
    let c , h' = usefulWildCompCaseInv' qss iss disj sss
    pure (c , MkUseful (h' ∷ []))


module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ {d}
  {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulWildMissCase' :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → Useful' (default_ P) (ps ∷ pss)
    → NonEmpty (Useful' P ((— ∷ ps) ∷ pss))
  usefulWildMissCase' (Left (Erased h)) ⟪ qs ∷ qss , is ∷ iss , disj , ss ∷ sss ⟫ =
    ⟪ (— ∷ qs) ∷ qss
    , (IWild {v = inhab} ∷ is) ∷ iss
    , default-preserves-#**⁻-wild h disj
    , (—⊆ ∷ ss) ∷ sss ⟫ ∷ []
  usefulWildMissCase' (Right hs) ⟪ qs ∷ qss , is ∷ iss , disj , ss ∷ sss ⟫ =
    fmap
      (λ where
        (c ⟨ h ⟩) →
          ⟪ (con c —* ∷ qs) ∷ qss
          , (con≼ (iWilds {vs = tabulateValues λ _ → nonEmptyAxiom}) ∷ is) ∷ iss
          , default-preserves-#**⁻ h disj
          , (—⊆ ∷ ss) ∷ sss ⟫)
      hs
  {-# COMPILE AGDA2HS usefulWildMissCase' #-}

  usefulWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → Useful (default_ P) (ps ∷ pss) → Useful P ((— ∷ ps) ∷ pss)
  usefulWildMissCase h (MkUseful hs) =
    MkUseful (hs >>= usefulWildMissCase' h)
  {-# COMPILE AGDA2HS usefulWildMissCase #-}

  usefulWildMissCaseInv' :
      Useful' P ((— ∷ ps) ∷ pss)
    → Useful' (default_ P) (ps ∷ pss)
  usefulWildMissCaseInv' ⟪ (q ∷ qs) ∷ qss , (i ∷ is) ∷ iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ qs ∷ qss , is ∷ iss , default-preserves-#** disj , ss ∷ sss ⟫

  usefulWildMissCaseInv :
      Useful P ((— ∷ ps) ∷ pss)
    → Useful (default_ P) (ps ∷ pss)
  usefulWildMissCaseInv (MkUseful hs) =
    MkUseful (fmap usefulWildMissCaseInv' hs)

module _
  ⦃ sig : Signature ⦄
  ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  decUseful' : (P : PatternMatrixStack αss) (ps : PatternStack αss)
    → @0 UsefulAcc P ps
    → DecP (Useful P ps)
  decUseful' {[]} []      [] done = Yes usefulNilOkCase
  decUseful' {[]} (_ ∷ _) [] done = No usefulNilBadCase
  decUseful' {[] ∷ αss} psss ([] ∷ pss) (step-tail h) =
    mapDecP usefulTailCase usefulTailCaseInv
      (decUseful' (map tailAll psss) pss h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((— ∷ ps) ∷ pss) (step-wild h h') =
    case decExistMissCon psss of λ where
      (Right miss) →
        mapDecP (usefulWildMissCase miss) usefulWildMissCaseInv
          (decUseful' (default_ psss) (ps ∷ pss) h)
      (Left (Erased comp)) →
        mapDecP usefulWildCompCase usefulWildCompCaseInv
          (decPAnyNameCon (dataDefs sig d) λ c →
            decUseful' (specialize c psss) (—* ∷ ps ∷ pss) (h' c (comp c)))
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((con c rs ∷ ps) ∷ pss) (step-con h) =
    mapDecP usefulConCase usefulConCaseInv
      (decUseful' (specialize c psss) (rs ∷ ps ∷ pss) h)
  decUseful' {(TyData d ∷ αs) ∷ αss} psss ((r₁ ∣ r₂ ∷ ps) ∷ pss) (step-∣ h h') =
    mapDecP usefulOrCase usefulOrCaseInv
      (theseDecP (decUseful' psss ((r₁ ∷ ps) ∷ pss) h) (decUseful' psss ((r₂ ∷ ps) ∷ pss) h'))
  {-# COMPILE AGDA2HS decUseful' #-}

  decUseful : (pss : PatternMatrix αs) (ps : Patterns αs)
    → DecP (Useful (map (_∷ []) pss) (ps ∷ []))
  decUseful pss ps =
    decUseful' (map (_∷ []) pss) (ps ∷ []) (∀UsefulAcc _ _)
  {-# COMPILE AGDA2HS decUseful #-}
