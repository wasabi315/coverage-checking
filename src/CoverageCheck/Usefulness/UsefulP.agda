open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.BranchSelection
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
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Usefulness

module _ ⦃ @0 sig : Signature ⦄ where

  _#*_ : (@0 ps qs : Patterns αs0) → Type
  ps #* qs = ∀ {vs} → ps ≼* vs → qs ≼* vs → ⊥

  _#**_ : (@0 P : PatternMatrix αs0) (@0 qs : Patterns αs0) → Type
  P #** qs = ∀ {vs} → P ≼** vs → qs ≼* vs → ⊥


module _ ⦃ @0 sig : Signature ⦄ (@0 P : PatternMatrix αs0) (@0 ps : Patterns αs0) where

  UsefulP' : Type
  UsefulP' = ∃[ qs ∈ Patterns αs0 ] (P #** qs) × (ps ⊆* qs)

  record UsefulP : Type where
    constructor MkUsefulP
    field
      witnesses : NonEmpty UsefulP'

  open UsefulP  public

  {-# COMPILE AGDA2HS UsefulP' inline  #-}
  {-# COMPILE AGDA2HS UsefulP  newtype #-}

--------------------------------------------------------------------------------
-- Properties of #** and specialize/default

module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {P : PatternMatrix (TyData d ◂ βs)}
  {rs₁ : Patterns αs} {rs₂ : Patterns βs}
  where

  specialize-preserves-#** :
    P #** (con c rs₁ ◂ rs₂) → specialize c P #** (rs₁ ◂◂ᵖ rs₂)
  specialize-preserves-#** disj iss is = case splitInstances rs₁ is of λ where
    ((vs₁ , vs₂) ⟨ refl , (is₁ , is₂) ⟩) →
      disj (specialize-preserves-≼⁻ iss) (con≼ is₁ ◂ is₂)

  specialize-preserves-#**⁻ :
    specialize c P #** (rs₁ ◂◂ᵖ rs₂) → P #** (con c rs₁ ◂ rs₂)
  specialize-preserves-#**⁻ disj {con c us ◂ vs} iss (con≼ is₁ ◂ is₂) =
    disj (specialize-preserves-≼ iss) (is₁ ◂◂ⁱ is₂)


module @0 _ ⦃ sig : Signature ⦄ {c : NameCon d}
  (let αs = argsTy (dataDefs sig d) c)
  {P : PatternMatrix (TyData d ◂ βs)}
  {rs : Patterns βs}
  where

  specialize-preserves-#**-wild :
    P #** (— ◂ rs) → specialize c P #** (—* ◂◂ᵖ rs)
  specialize-preserves-#**-wild disj iss is =
    case splitInstances {αs = argsTy (dataDefs sig d) c} —* is of λ where
      ((vs₁ , vs₂) ⟨ refl , (_ , is') ⟩) →
        disj (specialize-preserves-≼⁻ iss) (—≼ ◂ is')


module @0 _ ⦃ @0 sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  {P : PatternMatrix (TyData d ◂ αs)}
  {p : Pattern (TyData d)} {ps : Patterns αs}
  where

  default-preserves-#** : P #** (p ◂ ps) → default_ P #** ps
  default-preserves-#** disj iss is =
    disj (default-preserves-≼⁻ iss) (inst≼ _ ◂ is)


module @0 _ ⦃ @0 sig : Signature ⦄ {c : NameCon d} {qs : Patterns (argsTy (dataDefs sig d) c)} {rs : Patterns βs} where

  default-preserves-#**⁻ : {P : PatternMatrix (TyData d ◂ βs)}
    → c ∉** P
    → default_ P #** rs
    → P #** (con c qs ◂ rs)
  default-preserves-#**⁻ h disj {con c us ◂ vs} iss is@(con≼ is₁ ◂ is₂) =
    disj (default-preserves-≼ h iss) is₂


module @0 _ ⦃ @0 sig : Signature ⦄ {qs : Patterns βs} where

  default-preserves-#**⁻-wild : {P : PatternMatrix (TyData d ◂ βs)}
    → (∀ c → c ∉** P)
    → default_ P #** qs
    → P #** (— ◂ qs)
  default-preserves-#**⁻-wild h disj {con c us ◂ vs} iss is@(—≼ ◂ is₂) =
    disj (default-preserves-≼ (h c) iss) is₂

--------------------------------------------------------------------------------
-- Properties of usefulness


module _ ⦃ @0 sig : Signature ⦄ where

  usefulPNilOkCase : UsefulP [] ⌈⌉
  usefulPNilOkCase = MkUsefulP ((⌈⌉ ⟨ (λ ()) , ⌈⌉ ⟩) ◂ [])
  {-# COMPILE AGDA2HS usefulPNilOkCase #-}

  usefulPNilBadCase : {ps : Patterns ⌈⌉} {P : PatternMatrix ⌈⌉} → ¬ UsefulP (ps ∷ P) ⌈⌉
  usefulPNilBadCase {ps = ⌈⌉} (MkUsefulP ((⌈⌉ ⟨ h , _ ⟩) ◂ _)) =
    contradiction ⌈⌉ (h (here ⌈⌉))


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (α0 ◂ αs0)} {@0 r₁ r₂ : Pattern α0} {@0 ps : Patterns αs0} where

  usefulPOrCaseL' : UsefulP' P (r₁ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseL' ((q ◂ qs) ⟨ disj , b ◂ bs ⟩) =
    (q ◂ qs) ⟨ disj , (∣⊆ˡ b ◂ bs) ⟩
  {-# COMPILE AGDA2HS usefulPOrCaseL' transparent #-}

  usefulPOrCaseList : List (UsefulP' P (r₁ ◂ ps)) → List (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseList []       = []
  usefulPOrCaseList (h ∷ hs) = usefulPOrCaseL' h ∷ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseList transparent #-}

  usefulPOrCaseL : NonEmpty (UsefulP' P (r₁ ◂ ps)) → NonEmpty (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseL (h ◂ hs) = usefulPOrCaseL' h ◂ usefulPOrCaseList hs
  {-# COMPILE AGDA2HS usefulPOrCaseL transparent #-}

  usefulPOrCaseR' : UsefulP' P (r₂ ◂ ps) → UsefulP' P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCaseR' ((q ◂ qs) ⟨ disj , b ◂ bs ⟩) =
    (q ◂ qs) ⟨ disj , (∣⊆ʳ b ◂ bs) ⟩
  {-# COMPILE AGDA2HS usefulPOrCaseR' transparent #-}

  usefulPOrCaseRList : List (UsefulP' P (r₂ ◂ ps)) → List (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseRList []       = []
  usefulPOrCaseRList (h ∷ hs) = usefulPOrCaseR' h ∷ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseRList transparent #-}

  usefulPOrCaseR : NonEmpty (UsefulP' P (r₂ ◂ ps)) → NonEmpty (UsefulP' P (r₁ ∣ r₂ ◂ ps))
  usefulPOrCaseR (h ◂ hs) = usefulPOrCaseR' h ◂ usefulPOrCaseRList hs
  {-# COMPILE AGDA2HS usefulPOrCaseR transparent #-}

  usefulPOrCase : These (UsefulP P (r₁ ◂ ps)) (UsefulP P (r₂ ◂ ps)) → UsefulP P (r₁ ∣ r₂ ◂ ps)
  usefulPOrCase (This (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseL hs)
  usefulPOrCase (That (MkUsefulP hs)) = MkUsefulP (usefulPOrCaseR hs)
  usefulPOrCase (Both (MkUsefulP hs) (MkUsefulP hs')) = MkUsefulP (usefulPOrCaseL hs ◂◂ⁿᵉ usefulPOrCaseR hs')
  {-# COMPILE AGDA2HS usefulPOrCase #-}

  @0 usefulPOrCaseInv' : UsefulP' P (r₁ ∣ r₂ ◂ ps) → Either (UsefulP' P (r₁ ◂ ps)) (UsefulP' P (r₂ ◂ ps))
  usefulPOrCaseInv' (qs ⟨ disj , ∣⊆ˡ b ◂ bs ⟩) = Left (qs ⟨ disj , b ◂ bs ⟩)
  usefulPOrCaseInv' (qs ⟨ disj , ∣⊆ʳ b ◂ bs ⟩) = Right (qs ⟨ disj , b ◂ bs ⟩)

  @0 usefulPOrCaseInv : UsefulP P (r₁ ∣ r₂ ◂ ps) → These (UsefulP P (r₁ ◂ ps)) (UsefulP P (r₂ ◂ ps))
  usefulPOrCaseInv (MkUsefulP hs) = mapThese MkUsefulP MkUsefulP
    (partitionEithersNonEmpty (mapNonEmpty usefulPOrCaseInv' hs))


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {c : NameCon d} {@0 rs : Patterns (argsTy (dataDefs sig d) c)} {@0 ps : Patterns αs0} where

  usefulPConCase' : UsefulP' (specialize c P) (rs ◂◂ᵖ ps) → UsefulP' P (con c rs ◂ ps)
  usefulPConCase' (qs ⟨ disj , bs ⟩) =
    case splitBranchSelections rs bs of λ where
      ((qs₁ , qs₂) ⟨ refl , (bs₁ , bs₂) ⟩) →
        (con c qs₁ ◂ qs₂) ⟨ specialize-preserves-#**⁻ disj , (con⊆ bs₁ ◂ bs₂) ⟩
  {-# COMPILE AGDA2HS usefulPConCase' #-}

  usefulPConCase : UsefulP (specialize c P) (rs ◂◂ᵖ ps) → UsefulP P (con c rs ◂ ps)
  usefulPConCase (MkUsefulP hs) = MkUsefulP (mapNonEmpty usefulPConCase' hs)
  {-# COMPILE AGDA2HS usefulPConCase #-}


module _ ⦃ @0 sig : Signature ⦄ {@0 P : PatternMatrix (TyData d0 ◂ αs0)} {@0 c : NameCon d0} {@0 rs : Patterns (argsTy (dataDefs sig d0) c)} {@0 ps : Patterns αs0} where

  usefulPConCaseInv' : UsefulP' P (con c rs ◂ ps) → UsefulP' (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv' ((con c qs' ◂ qs) ⟨ disj , con⊆ bs' ◂ bs ⟩) =
    (qs' ◂◂ᵖ qs) ⟨ specialize-preserves-#** disj , (bs' ◂◂ᵇ bs) ⟩

  usefulPConCaseInv : UsefulP P (con c rs ◂ ps) → UsefulP (specialize c P) (rs ◂◂ᵖ ps)
  usefulPConCaseInv (MkUsefulP hs) = MkUsefulP (mapNonEmpty usefulPConCaseInv' hs)


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  where

  usefulPWildCompCase' : (c : NameCon d)
    → UsefulP' (specialize c P) (—* ◂◂ᵖ ps)
    → UsefulP' P (— ◂ ps)
  usefulPWildCompCase' c (qs ⟨ disj , bs ⟩) =
    case splitBranchSelections {αs = argsTy (dataDefs sig d) c} —* bs of λ where
      ((qs₁ , qs₂) ⟨ refl , (bs₁ , bs₂) ⟩) →
        (con c qs₁ ◂ qs₂) ⟨ specialize-preserves-#**⁻ disj , —⊆con bs₁ ◂ bs₂ ⟩
  {-# COMPILE AGDA2HS usefulPWildCompCase' #-}

  usefulPWildCompCase :
      NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
    → UsefulP P (— ◂ ps)
  usefulPWildCompCase hs = MkUsefulP do
    (c , MkUsefulP hs') ← hs
    mapNonEmpty (usefulPWildCompCase' c) hs'
  {-# COMPILE AGDA2HS usefulPWildCompCase #-}

  usefulPWildCompCaseInv' : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → UsefulP' P (— ◂ ps)
    → Σ[ c ∈ NameCon d ] UsefulP' (specialize c P) (—* ◂◂ᵖ ps)
  usefulPWildCompCaseInv' ((— ◂ qs) ⟨ disj , b ◂ bs ⟩) =
    inhabCon , ((—* ◂◂ᵖ qs) ⟨ (specialize-preserves-#**-wild disj , —⊆* ◂◂ᵇ bs) ⟩)
  usefulPWildCompCaseInv' ((con c qs' ◂ qs) ⟨ disj , —⊆con bs' ◂ bs ⟩) =
    (c , ((qs' ◂◂ᵖ qs) ⟨ (specialize-preserves-#** disj , bs' ◂◂ᵇ bs) ⟩))

  @0 usefulPWildCompCaseInv : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
    → UsefulP P (— ◂ ps)
    → NonEmpty (Σ[ c ∈ NameCon d ] UsefulP (specialize c P) (—* ◂◂ᵖ ps))
  usefulPWildCompCaseInv (MkUsefulP hs) =
    mapNonEmpty
      (λ h → case usefulPWildCompCaseInv' h of λ where
        (c , h') → c , MkUsefulP (h' ◂ [])
      )
      hs


module _ ⦃ sig : Signature ⦄ {d} {@0 P : PatternMatrix (TyData d ◂ αs0)} {@0 ps : Patterns αs0}
  ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
  where

  usefulPWildMissCase' :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP' (default_ P) ps
    → NonEmpty (UsefulP' P (— ◂ ps))
  usefulPWildMissCase' (Left (Erased h)) (vs ⟨ disj , bs ⟩) =
    ((— ◂ vs) ⟨ default-preserves-#**⁻-wild h disj , (—⊆ ◂ bs) ⟩) ◂ []
  usefulPWildMissCase' (Right hs) (qs ⟨ disj , bs ⟩) =
    mapNonEmpty
      (λ where
        (c ⟨ h ⟩) → (con c —* ◂ qs) ⟨ default-preserves-#**⁻ h disj , (—⊆con —⊆* ◂ bs) ⟩)
      hs
  {-# COMPILE AGDA2HS usefulPWildMissCase' #-}

  usefulPWildMissCase :
      Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P))
    → UsefulP (default_ P) ps → UsefulP P (— ◂ ps)
  usefulPWildMissCase h (MkUsefulP hs) =
    MkUsefulP (hs >>= usefulPWildMissCase' h)
  {-# COMPILE AGDA2HS usefulPWildMissCase #-}

  usefulPWildMissCaseInv' : UsefulP' P (— ◂ ps) → UsefulP' (default_ P) ps
  usefulPWildMissCaseInv' ((q ◂ qs) ⟨ disj , b ◂ bs ⟩) =
    qs ⟨ default-preserves-#** disj , bs ⟩

  usefulPWildMissCaseInv : UsefulP P (— ◂ ps) → UsefulP (default_ P) ps
  usefulPWildMissCaseInv (MkUsefulP hs) =
    MkUsefulP (mapNonEmpty usefulPWildMissCaseInv' hs)

--------------------------------------------------------------------------------

instance iUsefulPUseful : Usefulness UsefulP
iUsefulPUseful .nilOkCase       = usefulPNilOkCase
iUsefulPUseful .nilBadCase      = usefulPNilBadCase
iUsefulPUseful .orCase          = usefulPOrCase
iUsefulPUseful .orCaseInv       = usefulPOrCaseInv
iUsefulPUseful .conCase         = usefulPConCase
iUsefulPUseful .conCaseInv      = usefulPConCaseInv
iUsefulPUseful .wildMissCase    = usefulPWildMissCase
iUsefulPUseful .wildMissCaseInv = λ _ → usefulPWildMissCaseInv
iUsefulPUseful .wildCompCase    = λ _ → usefulPWildCompCase
iUsefulPUseful .wildCompCaseInv = λ _ → usefulPWildCompCaseInv
{-# COMPILE AGDA2HS iUsefulPUseful #-}
