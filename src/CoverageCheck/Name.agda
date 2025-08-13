open import CoverageCheck.Prelude

module CoverageCheck.Name where

--------------------------------------------------------------------------------

Name : Set
Name = String
{-# COMPILE AGDA2HS Name inline #-}

data In (x : Name) : (xs : List Name) → Set where
  InHere  : ∀ {xs} → In x (x ∷ xs)
  InThere : ∀ {y xs} → In x xs → In x (y ∷ xs)

NameIn : @0 List Name → Set
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

strengthenNameInFun : ∀ {@0 x : Name} {@0 xs : List Name} {@0 ℓ} {p : @0 NameIn (x ∷ xs) → Set ℓ}
  → ((y : NameIn (x ∷ xs)) → p y)
  → (((y ⟨ h ⟩) : NameIn xs) → p (y ⟨ InThere h ⟩))
strengthenNameInFun f (x ⟨ h ⟩) = f (x ⟨ InThere h ⟩)
{-# COMPILE AGDA2HS strengthenNameInFun #-}

allNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
allNameIn []       f = True
allNameIn (x ∷ xs) f = f (x ⟨ InHere ⟩) && allNameIn xs (strengthenNameInFun f)
{-# COMPILE AGDA2HS allNameIn #-}

decAllNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : ys ≡ xs)
  → {@0 p : NameIn ys → Set}
  → (∀ x → Dec (p x))
  → Either (Erase (∀ x → p x)) (Erase (∃[ x ∈ _ ] ¬ p x))
decAllNameIn []       refl f = Left (Erased λ _ → undefined)
decAllNameIn (x ∷ xs) refl {p} f =
  ifDec (f (x ⟨ InHere ⟩))
    (λ {{h}} → case decAllNameIn xs refl (strengthenNameInFun f) of λ
      { (Left (Erased h'))  → Left (Erased (lem1 h h'))
      ; (Right (Erased h')) → Right (Erased (lem2 h'))
      })
    (λ {{h}} → Right (Erased ((x ⟨ InHere ⟩) ⟨ h ⟩)))
  where
    @0 lem1 :
        p (x ⟨ InHere ⟩)
      → (((y ⟨ h ⟩) : NameIn xs) → p (y ⟨ InThere h ⟩))
      → (y : NameIn (x ∷ xs)) → p y
    lem1 h h' (y ⟨ InHere      ⟩) = h
    lem1 h h' (y ⟨ InThere h'' ⟩) = h' (y ⟨ h'' ⟩)

    @0 lem2 :
        ∃[ (y ⟨ h ⟩) ∈ NameIn xs ] ¬ p (y ⟨ InThere h ⟩)
      → ∃[ y ∈ NameIn (x ∷ xs) ] ¬ p y
    lem2 ((y ⟨ h ⟩) ⟨ h' ⟩) = (y ⟨ (InThere h) ⟩) ⟨ h' ⟩
{-# COMPILE AGDA2HS decAllNameIn #-}

anyNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
anyNameIn []       f = False
anyNameIn (x ∷ xs) f = f (x ⟨ InHere ⟩) || anyNameIn xs (strengthenNameInFun f)
{-# COMPILE AGDA2HS anyNameIn #-}

decAnyNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : ys ≡ xs)
  → {@0 p : NameIn ys → Set}
  → (∀ x → Dec (p x))
  → Dec (∃[ x ∈ _ ] p x)
decAnyNameIn []       refl     f = False ⟨ (λ _ → undefined) ⟩
decAnyNameIn (x ∷ xs) refl {p} f =
  mapDec
    (either
      (λ h → (x ⟨ InHere ⟩) ⟨ h ⟩)
      (λ { ((y ⟨ h ⟩) ⟨ h' ⟩) → (y ⟨ InThere h ⟩) ⟨ h' ⟩ }))
    lem
    (eitherDec (f (x ⟨ InHere ⟩)) (decAnyNameIn xs refl (strengthenNameInFun f)))
  where
    @0 lem : ∃[ y ∈ NameIn (x ∷ xs) ] p y
      → Either (p (x ⟨ InHere ⟩)) (∃[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩))
    lem ((y ⟨ InHere    ⟩) ⟨ h' ⟩) = Left h'
    lem ((y ⟨ InThere h ⟩) ⟨ h' ⟩) = Right ((y ⟨ h ⟩) ⟨ h' ⟩)
{-# COMPILE AGDA2HS decAnyNameIn #-}


decPAnyNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : ys ≡ xs)
  → {p : @0 NameIn ys → Set}
  → (∀ x → DecP (p x))
  → DecP (Σ[ x ∈ _ ] p x)
decPAnyNameIn [] refl f = No λ _ → undefined
decPAnyNameIn (x ∷ xs) refl {p} f =
  mapDecP
    (either
      (λ h → (x ⟨ InHere ⟩) , h )
      (λ { ((y ⟨ h ⟩) , h') → (y ⟨ InThere h ⟩) , h' }))
    lem
    (eitherDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl (strengthenNameInFun f)))
  where
    @0 lem : Σ[ y ∈ NameIn (x ∷ xs) ] p y
      → Either (p (x ⟨ InHere ⟩)) (Σ[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩))
    lem ((y ⟨ InHere    ⟩) , h') = Left h'
    lem ((y ⟨ InThere h ⟩) , h') = Right ((y ⟨ h ⟩) , h')
{-# COMPILE AGDA2HS decPAnyNameIn #-}


module @0 _ where
  private
    lem : {x : Name} {xs : List Name}
      → All (λ y → ¬ x ≡ y) xs
      → In x xs
      → ⊥
    lem (h ∷ hs) InHere      = h refl
    lem (h ∷ hs) (InThere p) = lem hs p

    fresh⇒uniqueIn : (x : Name) (xs : List Name)
      → Fresh xs
      → (p q : In x xs)
      → p ≡ q
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere      InHere      = refl
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) (InThere q) = cong InThere (fresh⇒uniqueIn x xs h' p q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere      (InThere q) = exFalso (lem h q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) InHere      = exFalso (lem h p)

  name-injective : {xs : List Name} {{_ : Fresh xs}}
    → {x y : NameIn xs} → value x ≡ value y → x ≡ y
  name-injective {xs} {{h}} {x ⟨ p ⟩} {y ⟨ q ⟩} refl
    rewrite fresh⇒uniqueIn x xs h p q
    = refl

instance
  -- import instances
  open import Haskell.Prim.Eq using ()
  open import Haskell.Law.Eq using ()

  iEqNameIn : {@0 xs : List Name} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = value x == value y

  @0 iLawfulEqNameIn : {@0 xs : List Name} {{_ : Fresh xs}} → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y
    = mapReflects name-injective (cong value) (isEquality (value x) (value y))
