open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness.Algorithm
open import CoverageCheck.Usefulness.Properties

module CoverageCheck.Usefulness.UsefulP
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
  infix 4 SubsumptionStack SubsumptionMatrixStack

  SubsumptionStack : {@0 αss : TyStack} → @0 PatternStack αss → @0 PatternStack αss → Type
  syntax SubsumptionStack pss vss = pss ⊆*ˢ vss
  pss ⊆*ˢ vss = HAll2 (λ ps vs → ps ⊆* vs) pss vss
  {-# COMPILE AGDA2HS SubsumptionStack inline #-}

  SubsumptionMatrixStack : {@0 αss : TyStack} → @0 PatternMatrixStack αss → @0 PatternStack αss → Type
  syntax SubsumptionMatrixStack psss vss = psss ⊆**ˢ vss
  psss ⊆**ˢ vss = Any (λ pss → pss ⊆*ˢ vss) psss
  {-# COMPILE AGDA2HS SubsumptionMatrixStack inline #-}


module _ ⦃ @0 sig : Signature ⦄
  (@0 P : PatternMatrixStack αss0) (@0 ps : PatternStack αss0)
  where

  -- ps is useful with respect to P iff there exists a pattern vector qs such that
  --   1. qs is not empty (that is, there exists a value vector vs that matches qs)
  --   2. all rows of P are disjoint from qs
  --   3. ps subsumes qs
  record UsefulP' : Type where
    constructor ⟪_,_,_,_⟫
    field
      qs       : PatternStack αss0
      @0 {vs}  : ValueStack αss0
      @0 qs≼vs : qs ≼*ˢ vs
      @0 P#qs  : P #** qs
      @0 ps⊆qs : ps ⊆*ˢ qs

  open UsefulP'

  record UsefulP : Type where
    constructor MkUsefulP
    field
      witnesses : NonEmpty UsefulP'

  open UsefulP public

  {-# COMPILE AGDA2HS UsefulP' unboxed #-}
  {-# COMPILE AGDA2HS UsefulP  newtype #-}

--------------------------------------------------------------------------------
-- Properties of usefulness


module _ ⦃ @0 sig : Signature ⦄ where

  usefulPNilOkCase : UsefulP [] []
  usefulPNilOkCase = MkUsefulP (⟪ [] , [] , (λ ()) , [] ⟫ ∷ [])
  {-# COMPILE AGDA2HS usefulPNilOkCase #-}

  usefulPNilBadCase : {ps : PatternStack []} {P : PatternMatrixStack []} → ¬ UsefulP (ps ∷ P) []
  usefulPNilBadCase {ps = []} (MkUsefulP (⟪ [] , _ , h , _ ⟫ ∷ _)) =
    contradiction [] (h (here []))


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ([] ∷ αss0)} {@0 pss : PatternStack αss0}
  where

  usefulPTailCase' : UsefulP' (map tailAll P) pss → UsefulP' P ([] ∷ pss)
  usefulPTailCase' ⟪ qss , iss , disj , sss ⟫ =
    ⟪ [] ∷ qss , [] ∷ iss , #**-tail⁻ disj , [] ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulPTailCase' inline #-}

  usefulPTailCase : UsefulP (map tailAll P) pss → UsefulP P ([] ∷ pss)
  usefulPTailCase (MkUsefulP hs) = MkUsefulP (fmap usefulPTailCase' hs)
  {-# COMPILE AGDA2HS usefulPTailCase #-}

  usefulPTailCaseInv' : UsefulP' P ([] ∷ pss) → UsefulP' (map tailAll P) pss
  usefulPTailCaseInv' ⟪ [] ∷ qss , [] ∷ iss , disj , [] ∷ sss ⟫ =
    ⟪ qss , iss , #**-tail disj , sss ⟫

  usefulPTailCaseInv : UsefulP P ([] ∷ pss) → UsefulP (map tailAll P) pss
  usefulPTailCaseInv (MkUsefulP hs) = MkUsefulP (fmap usefulPTailCaseInv' hs)


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((α0 ∷ αs0) ∷ αss0)}
  {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulPOrCaseL' : UsefulP' P ((r₁ ∷ ps) ∷ pss) → UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulPOrCaseL' ⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulPOrCaseL' transparent #-}

  usefulPOrCaseList : List (UsefulP' P ((r₁ ∷ ps) ∷ pss)) → List (UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulPOrCaseList []       = []
  usefulPOrCaseList (h ∷ hs) = usefulPOrCaseL' h ∷ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseList transparent #-}

  usefulPOrCaseL : NonEmpty (UsefulP' P ((r₁ ∷ ps) ∷ pss)) → NonEmpty (UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulPOrCaseL (h ∷ hs) = usefulPOrCaseL' h ∷ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseL transparent #-}

  usefulPOrCaseR' : UsefulP' P ((r₂ ∷ ps) ∷ pss) → UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulPOrCaseR' ⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulPOrCaseR' transparent #-}

  usefulPOrCaseRList : List (UsefulP' P ((r₂ ∷ ps) ∷ pss)) → List (UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulPOrCaseRList []       = []
  usefulPOrCaseRList (h ∷ hs) = usefulPOrCaseR' h ∷ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseRList transparent #-}

  usefulPOrCaseR : NonEmpty (UsefulP' P ((r₂ ∷ ps) ∷ pss)) → NonEmpty (UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss))
  usefulPOrCaseR (h ∷ hs) = usefulPOrCaseR' h ∷ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseR transparent #-}

  usefulPOrCase :
      These (UsefulP P ((r₁ ∷ ps) ∷ pss)) (UsefulP P ((r₂ ∷ ps) ∷ pss))
    → UsefulP P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
  usefulPOrCase (This (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseL hs)
  usefulPOrCase (That (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseR hs)
  usefulPOrCase (Both (MkUsefulP hs) (MkUsefulP hs')) = MkUsefulP (usefulPOrCaseL hs <> usefulPOrCaseR hs')
  {-# COMPILE AGDA2HS usefulPOrCase #-}

  @0 usefulPOrCaseInv' :
      UsefulP' P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → Either (UsefulP' P ((r₁ ∷ ps) ∷ pss)) (UsefulP' P ((r₂ ∷ ps) ∷ pss))
  usefulPOrCaseInv' ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ˡ s ∷ ss) ∷ sss ⟫ =
    Left (⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫)
  usefulPOrCaseInv' ⟪ (q ∷ qs) ∷ qss , iss , disj , (∣⊆ʳ s ∷ ss) ∷ sss ⟫ =
    Right (⟪ (q ∷ qs) ∷ qss , iss , disj , (s ∷ ss) ∷ sss ⟫)

  @0 usefulPOrCaseInv :
      UsefulP P ((r₁ ∣ r₂ ∷ ps) ∷ pss)
    → These (UsefulP P ((r₁ ∷ ps) ∷ pss)) (UsefulP P ((r₂ ∷ ps) ∷ pss))
  usefulPOrCaseInv (MkUsefulP hs) = mapThese MkUsefulP MkUsefulP
    (partitionEithersNonEmpty (fmap usefulPOrCaseInv' hs))


module _ ⦃ @0 sig : Signature ⦄ {c : NameCon d0}
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulPConCase' :
      UsefulP' (specialize c P) (rs ∷ ps ∷ pss)
    → UsefulP' P ((con c rs ∷ ps) ∷ pss)
  usefulPConCase' ⟪ qs' ∷ qs ∷ qss , is' ∷ is ∷ iss , disj , ss' ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , (con≼ is' ∷ is) ∷ iss
    , specialize-preserves-#**⁻ disj
    , (con⊆ ss' ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulPConCase' #-}

  usefulPConCase :
      UsefulP (specialize c P) (rs ∷ ps ∷ pss)
    → UsefulP P ((con c rs ∷ ps) ∷ pss)
  usefulPConCase (MkUsefulP hs) = MkUsefulP (fmap usefulPConCase' hs)
  {-# COMPILE AGDA2HS usefulPConCase #-}

  usefulPConCaseInv' :
      UsefulP' P ((con c rs ∷ ps) ∷ pss)
    → UsefulP' (specialize c P) (rs ∷ ps ∷ pss)
  usefulPConCaseInv' ⟪ (con c qs' ∷ qs) ∷ qss , (con≼ is' ∷ is) ∷ iss , disj , (con⊆ ss' ∷ ss) ∷ sss ⟫ =
    ⟪ qs' ∷ qs ∷ qss
    , is' ∷ is ∷ iss
    , specialize-preserves-#** disj
    , ss' ∷ ss ∷ sss ⟫

  usefulPConCaseInv :
      UsefulP P ((con c rs ∷ ps) ∷ pss)
    → UsefulP (specialize c P) (rs ∷ ps ∷ pss)
  usefulPConCaseInv (MkUsefulP hs) = MkUsefulP (fmap usefulPConCaseInv' hs)


module _ ⦃ @0 sig : Signature ⦄
  {@0 P : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulPWildCompCase' : (c : NameCon d0)
    → UsefulP' (specialize c P) (—* ∷ ps ∷ pss)
    → UsefulP' P ((— ∷ ps) ∷ pss)
  usefulPWildCompCase' c ⟪ qs' ∷ qs ∷ qss , is' ∷ is ∷ iss , disj , _ ∷ ss ∷ sss ⟫ =
    ⟪ (con c qs' ∷ qs) ∷ qss
    , (con≼ is' ∷ is) ∷ iss
    , specialize-preserves-#**⁻ disj
    , (—⊆ ∷ ss) ∷ sss ⟫
  {-# COMPILE AGDA2HS usefulPWildCompCase' #-}

  usefulPWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulP (specialize c P) (—* ∷ ps ∷ pss))
    → UsefulP P ((— ∷ ps) ∷ pss)
  usefulPWildCompCase hs = MkUsefulP do
    c , MkUsefulP hs' ← hs
    fmap (usefulPWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulPWildCompCase #-}

  @0 usefulPWildCompCaseInv' : ∀ qss {vss}
    → qss ≼*ˢ vss
    → P #** qss
    → ((— ∷ ps) ∷ pss) ⊆*ˢ qss
    → Σ[ c ∈ NameCon d0 ] UsefulP' (specialize c P) (—* ∷ ps ∷ pss)
  usefulPWildCompCaseInv' ((— ∷ qs) ∷ qss) {(con c vs' ∷ vs) ∷ vss} ((i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    c , ⟪ —* ∷ qs ∷ qss
        , iWilds {vs = vs'} ∷ is ∷ iss
        , specialize-preserves-#**-wild disj
        , —⊆* ∷ ss ∷ sss ⟫
  usefulPWildCompCaseInv' ((con c qs' ∷ qs) ∷ qss) ((con≼ is' ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    c , ⟪ qs' ∷ qs ∷ qss
        , is' ∷ is ∷ iss
        , specialize-preserves-#** disj
        , —⊆* ∷ ss ∷ sss ⟫
  usefulPWildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) ((∣≼ˡ i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    usefulPWildCompCaseInv' ((q₁ ∷ qs) ∷ qss) ((i ∷ is) ∷ iss) (#-∣ˡ disj) ((—⊆ ∷ ss) ∷ sss)
  usefulPWildCompCaseInv' ((q₁ ∣ q₂ ∷ qs) ∷ qss) ((∣≼ʳ i ∷ is) ∷ iss) disj ((s ∷ ss) ∷ sss) =
    usefulPWildCompCaseInv' ((q₂ ∷ qs) ∷ qss) ((i ∷ is) ∷ iss) (#-∣ʳ disj) ((—⊆ ∷ ss) ∷ sss)

  @0 usefulPWildCompCaseInv :
      UsefulP P ((— ∷ ps) ∷ pss)
    → NonEmpty (Σ[ c ∈ NameCon d0 ] UsefulP (specialize c P) (—* ∷ ps ∷ pss))
  usefulPWildCompCaseInv (MkUsefulP hs) = do
    ⟪ qss , iss , disj , sss ⟫ ← hs
    let c , h' = usefulPWildCompCaseInv' qss iss disj sss
    pure (c , MkUsefulP (h' ∷ []))


module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ {d}
  {@0 P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0)}
  {@0 ps : Patterns αs0} {@0 pss : PatternStack αss0}
  where

  usefulPWildMissCase' :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP' (default_ P) (ps ∷ pss)
    → NonEmpty (UsefulP' P ((— ∷ ps) ∷ pss))
  usefulPWildMissCase' (Left (Erased h)) ⟪ qs ∷ qss , is ∷ iss , disj , ss ∷ sss ⟫ =
    ⟪ (— ∷ qs) ∷ qss
    , (IWild {v = inhab} ∷ is) ∷ iss
    , default-preserves-#**⁻-wild h disj
    , (—⊆ ∷ ss) ∷ sss ⟫ ∷ []
  usefulPWildMissCase' (Right hs) ⟪ qs ∷ qss , is ∷ iss , disj , ss ∷ sss ⟫ =
    fmap
      (λ where
        (c ⟨ h ⟩) →
          ⟪ (con c —* ∷ qs) ∷ qss
          , (con≼ (iWilds {vs = tabulateValues λ _ → nonEmptyAxiom}) ∷ is) ∷ iss
          , default-preserves-#**⁻ h disj
          , (—⊆ ∷ ss) ∷ sss ⟫)
      hs
  {-# COMPILE AGDA2HS usefulPWildMissCase' #-}

  usefulPWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP (default_ P) (ps ∷ pss) → UsefulP P ((— ∷ ps) ∷ pss)
  usefulPWildMissCase h (MkUsefulP hs) =
    MkUsefulP (hs >>= usefulPWildMissCase' h)
  {-# COMPILE AGDA2HS usefulPWildMissCase #-}

  usefulPWildMissCaseInv' :
      UsefulP' P ((— ∷ ps) ∷ pss)
    → UsefulP' (default_ P) (ps ∷ pss)
  usefulPWildMissCaseInv' ⟪ (q ∷ qs) ∷ qss , (i ∷ is) ∷ iss , disj , (s ∷ ss) ∷ sss ⟫ =
    ⟪ qs ∷ qss , is ∷ iss , default-preserves-#** disj , ss ∷ sss ⟫

  usefulPWildMissCaseInv :
      UsefulP P ((— ∷ ps) ∷ pss)
    → UsefulP (default_ P) (ps ∷ pss)
  usefulPWildMissCaseInv (MkUsefulP hs) =
    MkUsefulP (fmap usefulPWildMissCaseInv' hs)

--------------------------------------------------------------------------------

instance iUsefulPUseful : Usefulness UsefulP
iUsefulPUseful .nilOkCase       = usefulPNilOkCase
iUsefulPUseful .nilBadCase      = usefulPNilBadCase
iUsefulPUseful .tailCase        = usefulPTailCase
iUsefulPUseful .tailCaseInv     = usefulPTailCaseInv
iUsefulPUseful .orCase          = usefulPOrCase
iUsefulPUseful .orCaseInv       = usefulPOrCaseInv
iUsefulPUseful .conCase         = usefulPConCase
iUsefulPUseful .conCaseInv      = usefulPConCaseInv
iUsefulPUseful .wildMissCase    = usefulPWildMissCase
iUsefulPUseful .wildMissCaseInv = λ _ → usefulPWildMissCaseInv
iUsefulPUseful .wildCompCase    = λ _ → usefulPWildCompCase
iUsefulPUseful .wildCompCaseInv = λ _ → usefulPWildCompCaseInv
{-# COMPILE AGDA2HS iUsefulPUseful #-}
