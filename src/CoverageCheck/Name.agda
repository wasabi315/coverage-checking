open import CoverageCheck.Prelude

module CoverageCheck.Name where

{-# FOREIGN AGDA2HS import Prelude hiding (null) #-}

--------------------------------------------------------------------------------

Name : Set
Name = String
{-# COMPILE AGDA2HS Name #-}

data In (x : Name) : (xs : List Name) → Set where
  InHere  : ∀ {xs} →  In x (x ∷ xs)
  InThere : ∀ {y xs} → In x xs → In x (y ∷ xs)

NameIn : @0 List Name → Set
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

module _ where
  private
    @0 All≢⇒¬InHere : ∀ {x xs}
      → All (λ y → ¬ x ≡ y) xs
      → ¬ In x xs
    All≢⇒¬InHere (h ◂ hs) InHere        = h refl
    All≢⇒¬InHere (h ◂ hs) (InThere hs') = All≢⇒¬InHere hs hs'

    @0 fresh⇒uniqueIn : (x : Name) (xs : List Name)
      → Fresh xs
      → (p q : In x xs)
      → p ≡ q
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere InHere = refl
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) (InThere q) = cong InThere (fresh⇒uniqueIn x xs h' p q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') InHere (InThere q) = explode (All≢⇒¬InHere h q)
    fresh⇒uniqueIn x (y ∷ xs) (h , h') (InThere p) InHere = explode (All≢⇒¬InHere h p)

  @0 name-injective : ∀ {@0 xs} ⦃ @0 _ : Fresh xs ⦄ {x y : NameIn xs}
    → value x ≡ value y
    → x ≡ y
  name-injective {xs} ⦃ h ⦄ {x ⟨ p ⟩} {y ⟨ q ⟩} refl
    = cong (x ⟨_⟩) (fresh⇒uniqueIn x xs h p q)

--------------------------------------------------------------------------------

instance
  -- import instances
  open import Haskell.Prim.Eq using ()
  open import Haskell.Law.Eq using ()
  open import Haskell.Prim.Ord using (_<_)

  iEqNameIn : {@0 xs : List Name} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = value x == value y

  @0 iLawfulEqNameIn : {@0 xs : List Name} ⦃ _ : Fresh xs ⦄ → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y
    = mapReflects name-injective (cong value) (isEquality (value x) (value y))

  iOrdFromLessThanNameIn : {@0 xs : List Name} → OrdFromLessThan (NameIn xs)
  iOrdFromLessThanNameIn .OrdFromLessThan._<_ x y = value x < value y

  iOrdNameIn : {@0 xs : List Name} → Ord (NameIn xs)
  iOrdNameIn = record {OrdFromLessThan iOrdFromLessThanNameIn}

--------------------------------------------------------------------------------

universalNameInListAux : (xs : List Name) {@0 ys : List Name}
  → (@0 weaken : ∀ {@0 x} → In x xs → In x ys)
  → List (NameIn ys)
universalNameInListAux []       weaken = []
universalNameInListAux (x ∷ xs) weaken =
  (x ⟨ weaken InHere ⟩) ∷ universalNameInListAux xs (weaken ∘ InThere)
{-# COMPILE AGDA2HS universalNameInListAux transparent #-}

universalNameInList : (xs : List Name) → List (NameIn xs)
universalNameInList xs = universalNameInListAux xs id
{-# COMPILE AGDA2HS universalNameInList inline #-}

@0 universalNameInListUniversalAux : (xs : List Name) {@0 ys : List Name}
  → (@0 weaken : ∀ {@0 x} → In x xs → In x ys)
  → ∀ ((y ⟨ h ⟩) : NameIn xs)
  → elem (y ⟨ weaken h ⟩) (universalNameInListAux xs weaken) ≡ True
universalNameInListUniversalAux (x ∷ xs) weaken (y ⟨ InHere ⟩) rewrite eqReflexivity x = refl
universalNameInListUniversalAux (x ∷ xs) weaken (y ⟨ InThere h ⟩) =
  let ih = universalNameInListUniversalAux xs (weaken ∘ InThere) (y ⟨ h ⟩) in
  subst (λ b → (y == x || b) ≡ True) (sym ih) (prop-x-||-True (y == x))

@0 universalNameInListUniversal : (xs : List Name)
  → ∀ x → elem x (universalNameInList xs) ≡ True
universalNameInListUniversal xs x = universalNameInListUniversalAux xs id x

universalNameInSet : (xs : List Name) → Set' (NameIn xs)
universalNameInSet xs = fromList (universalNameInList xs)
{-# COMPILE AGDA2HS universalNameInSet inline #-}

@0 universalNameInSetUniversal : (xs : List Name)
  → ∀ x → member x (universalNameInSet xs) ≡ True
universalNameInSetUniversal xs x rewrite prop-member-fromList x (universalNameInList xs)
  = universalNameInListUniversal xs x

@0 universalNameInSetUniversal' : {xs : List Name} (s : Set' (NameIn xs))
  → null (difference (universalNameInSet xs) s) ≡ True
  → ∀ x → member x s ≡ True
universalNameInSetUniversal' {xs} s eq x =
  prop-difference-empty (prop-null→empty _ eq) (universalNameInSetUniversal xs x)

--------------------------------------------------------------------------------

strengthenNameInFun : ∀ {@0 x : Name} {@0 xs : List Name} {@0 ℓ} {p : @0 NameIn (x ∷ xs) → Set ℓ}
  → ((y : NameIn (x ∷ xs)) → p y)
  → ((y ⟨ h ⟩) : NameIn xs) → p (y ⟨ InThere h ⟩)
strengthenNameInFun f = λ where (x ⟨ h ⟩) → f (x ⟨ InThere h ⟩)
{-# COMPILE AGDA2HS strengthenNameInFun inline #-}

module _ {@0 xs} (f : NameIn xs → Bool) where

  anyNameInAux : (ys : List Name)
    → (@0 weaken : ∀ {@0 x} → In x ys → In x xs)
    → Bool
  anyNameInAux []       weaken = False
  anyNameInAux (x ∷ ys) weaken =
    f (x ⟨ weaken InHere ⟩) || anyNameInAux ys (weaken ∘ InThere)
  {-# COMPILE AGDA2HS anyNameInAux #-}


anyNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
anyNameIn xs f = anyNameInAux f xs id
{-# COMPILE AGDA2HS anyNameIn inline #-}


decPAnyNameIn : (xs : List Name)
  → {@0 ys : List Name} (@0 eq : xs ≡ ys)
  → {p : @0 NameIn ys → Set}
  → (∀ x → DecP (p x))
  → DecP (Σ[ x ∈ _ ] p x)
decPAnyNameIn []       refl     f = No λ _ → undefined
decPAnyNameIn (x ∷ xs) refl {p} f =
  mapDecP
    (either (λ h → lem1 h) lem2)
    lem3
    (eitherDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl (strengthenNameInFun f)))
  where
    lem1 : p (x ⟨ InHere ⟩) → Σ[ y ∈ NameIn (x ∷ xs) ] p y
    lem1 h = (x ⟨ InHere ⟩ , h)

    lem2 : _
    lem2 = λ where ((y ⟨ h ⟩) , h') → (y ⟨ InThere h ⟩) , h'

    @0 lem3 : Σ[ y ∈ NameIn (x ∷ xs) ] p y
      → Either (p (x ⟨ InHere ⟩)) (Σ[ (y ⟨ h ⟩) ∈ NameIn xs ] p (y ⟨ InThere h ⟩))
    lem3 ((y ⟨ InHere ⟩) , h') = Left h'
    lem3 ((y ⟨ InThere h ⟩) , h') = Right ((y ⟨ h ⟩) , h')
{-# COMPILE AGDA2HS decPAnyNameIn #-}
