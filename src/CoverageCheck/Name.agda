open import CoverageCheck.Prelude

module CoverageCheck.Name where

--------------------------------------------------------------------------------

Name : Set
Name = String
{-# COMPILE AGDA2HS Name #-}

data In (x : Name) : (xs : List Name) → Set where
  InHere  : ∀ {xs} → In x (x ∷ xs)
  InThere : ∀ {y xs} → In x xs → In x (y ∷ xs)

NameIn : @0 List Name → Set
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

strengthenNameInFun : ∀ {@0 x : Name} {@0 xs : List Name} {@0 ℓ} {p : @0 NameIn (x ∷ xs) → Set ℓ}
  → ((y : NameIn (x ∷ xs)) → p y)
  → ((y ⟨ h ⟩) : NameIn xs) → p (y ⟨ InThere h ⟩)
strengthenNameInFun f = λ where (x ⟨ h ⟩) → f (x ⟨ InThere h ⟩)
{-# COMPILE AGDA2HS strengthenNameInFun inline #-}

allNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
allNameIn []       f = True
allNameIn (x ∷ xs) f = f (x ⟨ InHere ⟩) && allNameIn xs (strengthenNameInFun f)
{-# COMPILE AGDA2HS allNameIn #-}

anyNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
anyNameIn []       f = False
anyNameIn (x ∷ xs) f = f (x ⟨ InHere ⟩) || anyNameIn xs (strengthenNameInFun f)
{-# COMPILE AGDA2HS anyNameIn #-}

decAllNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : xs ≡ ys)
  → {@0 p : NameIn ys → Set}
  → ((x : NameIn ys) → Dec (p x))
  → Either (Erase (∀ x → p x)) (NonEmpty (∃[ x ∈ NameIn ys ] ¬ p x))
decAllNameIn []       refl {p} f = Left (Erased λ _ → undefined)
decAllNameIn (x ∷ xs) refl {p} f = ifDec (f (x ⟨ InHere ⟩))
  (λ ⦃ h ⦄ → case decAllNameIn xs refl (strengthenNameInFun f) of λ where
    (Left (Erased h')) → Left (Erased (lem1 h h'))
    (Right h') → Right (mapNonEmpty lem2 h'))
  (λ ⦃ h ⦄ → case decAllNameIn xs refl (strengthenNameInFun f) of λ where
    (Left _) → Right (((x ⟨ InHere ⟩) ⟨ h ⟩) ◂ [])
    (Right h') → Right (((x ⟨ InHere ⟩) ⟨ h ⟩) ◂′ mapNonEmpty lem2 h'))
  where
    @0 lem1 :
        p (x ⟨ InHere ⟩)
      → (((y ⟨ h ⟩) : NameIn xs) → p (y ⟨ InThere h ⟩))
      → (y : NameIn (x ∷ xs)) → p y
    lem1 h h' (y ⟨ InHere      ⟩) = h
    lem1 h h' (y ⟨ InThere h'' ⟩) = h' (y ⟨ h'' ⟩)

    lem2 :
        ∃[ (y ⟨ h ⟩) ∈ NameIn xs ] ¬ p (y ⟨ InThere h ⟩)
      → ∃[ y ∈ NameIn (x ∷ xs) ] ¬ p y
    lem2 ((y ⟨ h ⟩) ⟨ h' ⟩) = (y ⟨ (InThere h) ⟩) ⟨ h' ⟩
{-# COMPILE AGDA2HS decAllNameIn #-}

decAnyNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : xs ≡ ys)
  → {@0 p : NameIn ys → Set}
  → (∀ x → Dec (p x))
  → Dec (NonEmpty (∃[ x ∈ _ ] p x))
decAnyNameIn []       refl     f = False ⟨ (λ _ → undefined) ⟩
decAnyNameIn (x ∷ xs) refl {p} f =
  mapDec
    (these (λ h → lem1 h ◂ []) lem2 (λ h hs → lem1 h ◂′ lem2 hs))
    lem4
    (theseDec (f (x ⟨ InHere ⟩)) (decAnyNameIn xs refl (strengthenNameInFun f)))
  where
    @0 lem1 : p (x ⟨ InHere ⟩) → ∃[ y ∈ NameIn (x ∷ xs) ] p y
    lem1 h = (x ⟨ InHere ⟩) ⟨ h ⟩

    @0 lem2 : _
    lem2 = mapNonEmpty (λ where ((y ⟨ h ⟩) ⟨ h' ⟩) → (y ⟨ InThere h ⟩) ⟨ h' ⟩)

    @0 lem3 : ∃[ y ∈ NameIn (x ∷ xs) ] p y
      → Either (p (x ⟨ InHere ⟩)) (∃[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩))
    lem3 ((y ⟨ InHere    ⟩) ⟨ h' ⟩) = Left h'
    lem3 ((y ⟨ InThere h ⟩) ⟨ h' ⟩) = Right ((y ⟨ h ⟩) ⟨ h' ⟩)

    @0 lem4 : NonEmpty (∃[ y ∈ NameIn (x ∷ xs) ] p y)
      → These (p (x ⟨ InHere ⟩)) (NonEmpty (∃[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩)))
    lem4 hs = mapThese head id (partitionEither (mapNonEmpty lem3 hs))
{-# COMPILE AGDA2HS decAnyNameIn #-}

decPAnyNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : xs ≡ ys)
  → {p : @0 NameIn ys → Set}
  → (∀ x → DecP (p x))
  → DecP (NonEmpty (Σ[ x ∈ _ ] p x))
decPAnyNameIn []       refl     f = No λ _ → undefined
decPAnyNameIn (x ∷ xs) refl {p} f =
  mapDecP
    (these (λ h → lem1 h ◂ []) lem2 (λ h hs → lem1 h ◂′ lem2 hs))
    lem4
    (theseDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl (strengthenNameInFun f)))
  where
    lem1 : p (x ⟨ InHere ⟩) → Σ[ y ∈ NameIn (x ∷ xs) ] p y
    lem1 h = (x ⟨ InHere ⟩ , h)

    lem2 : _
    lem2 = mapNonEmpty (λ where ((y ⟨ h ⟩) , h') → (y ⟨ InThere h ⟩) , h')

    @0 lem3 : Σ[ y ∈ NameIn (x ∷ xs) ] p y
      → Either (p (x ⟨ InHere ⟩)) (Σ[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩))
    lem3 ((y ⟨ InHere    ⟩) , h') = Left h'
    lem3 ((y ⟨ InThere h ⟩) , h') = Right ((y ⟨ h ⟩) , h')

    @0 lem4 : NonEmpty (Σ[ y ∈ NameIn (x ∷ xs) ] p y)
      → These (p (x ⟨ InHere ⟩)) (NonEmpty (Σ[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩)))
    lem4 hs = mapThese head id (partitionEither (mapNonEmpty lem3 hs))
{-# COMPILE AGDA2HS decPAnyNameIn #-}

module _ where
  private
    @0 lem : {x : Name} {xs : List Name}
      → All (λ y → ¬ x ≡ y) xs
      → ¬ In x xs
    lem (h ◂ hs) InHere      = h refl
    lem (h ◂ hs) (InThere p) = lem hs p

    @0 fresh⇒uniqueIn : (x : Name) (xs : List Name)
      → Fresh xs
      → (p q : In x xs)
      → p ≡ q
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere      InHere      = refl
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) (InThere q) = cong InThere (fresh⇒uniqueIn x xs h' p q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere      (InThere q) = exFalso (lem h q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) InHere      = exFalso (lem h p)

  @0 nameInjective : ∀ {@0 xs} ⦃ @0 _ : Fresh xs ⦄ {x y : NameIn xs}
    → value x ≡ value y
    → x ≡ y
  nameInjective {xs} ⦃ h ⦄ {x ⟨ p ⟩} {y ⟨ q ⟩} refl
    = cong (x ⟨_⟩) (fresh⇒uniqueIn x xs h p q)


instance
  -- import instances
  open import Haskell.Prim.Eq using ()
  open import Haskell.Law.Eq using ()

  iEqNameIn : {@0 xs : List Name} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = value x == value y

  @0 iLawfulEqNameIn : {@0 xs : List Name} ⦃ _ : Fresh xs ⦄ → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y
    = mapReflects nameInjective (cong value) (isEquality (value x) (value y))
