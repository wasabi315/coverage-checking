open import CoverageCheck.Prelude
open import Data.Set as Set using (Set)

module CoverageCheck.Name where

--------------------------------------------------------------------------------

Name : Type
Name = String
{-# COMPILE AGDA2HS Name #-}

data In (x : Name) : (xs : List Name) → Type where
  InHere  : ∀ {xs} →  In x (x ∷ xs)
  InThere : ∀ {y xs} → In x xs → In x (y ∷ xs)

NameIn : @0 List Name → Type
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

universalNameInList' : (xs : List Name) {@0 ys : List Name}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → List (NameIn ys)
universalNameInList' []       inj = []
universalNameInList' (x ∷ xs) inj =
  (x ⟨ inj InHere ⟩) ∷ universalNameInList' xs (inj ∘ InThere)
{-# COMPILE AGDA2HS universalNameInList' transparent #-}

universalNameInList : (xs : List Name) → List (NameIn xs)
universalNameInList xs = universalNameInList' xs id
{-# COMPILE AGDA2HS universalNameInList inline #-}

@0 universalNameInListUniversal' : (xs : List Name) {@0 ys : List Name}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → ∀ ((y ⟨ h ⟩) : NameIn xs)
  → elem (y ⟨ inj h ⟩) (universalNameInList' xs inj) ≡ True
universalNameInListUniversal' (x ∷ xs) inj (y ⟨ InHere ⟩) rewrite eqReflexivity x = refl
universalNameInListUniversal' (x ∷ xs) inj (y ⟨ InThere h ⟩) =
  let ih = universalNameInListUniversal' xs (inj ∘ InThere) (y ⟨ h ⟩) in
  subst (λ b → (y == x || b) ≡ True) (sym ih) (prop-x-||-True (y == x))

@0 universalNameInListUniversal : (xs : List Name)
  → ∀ x → elem x (universalNameInList xs) ≡ True
universalNameInListUniversal xs x = universalNameInListUniversal' xs id x

universalNameInSet : (xs : List Name) → Set (NameIn xs)
universalNameInSet xs = Set.fromList (universalNameInList xs)
{-# COMPILE AGDA2HS universalNameInSet inline #-}

@0 universalNameInSetUniversal : (xs : List Name)
  → ∀ x → Set.member x (universalNameInSet xs) ≡ True
universalNameInSetUniversal xs x rewrite prop-member-fromList x (universalNameInList xs)
  = universalNameInListUniversal xs x

@0 universalNameInSetUniversal' : {xs : List Name} (s : Set (NameIn xs))
  → Set.null (Set.difference (universalNameInSet xs) s) ≡ True
  → ∀ x → Set.member x s ≡ True
universalNameInSetUniversal' {xs} s eq x =
  prop-difference-empty (prop-null→empty _ eq) (universalNameInSetUniversal xs x)

--------------------------------------------------------------------------------

module _ {@0 xs} (f : NameIn xs → Bool) where

  anyNameIn' : (ys : List Name)
    → (@0 inj : ∀ {@0 x} → In x ys → In x xs)
    → Bool
  anyNameIn' []       inj = False
  anyNameIn' (x ∷ ys) inj =
    f (x ⟨ inj InHere ⟩) || anyNameIn' ys (inj ∘ InThere)
  {-# COMPILE AGDA2HS anyNameIn' #-}


anyNameIn : (xs : List Name) → (NameIn xs → Bool) → Bool
anyNameIn xs f = anyNameIn' f xs id
{-# COMPILE AGDA2HS anyNameIn inline #-}

module _ where
  private
    lem1 : ∀ {x} {@0 xs} {p : @0 NameIn (x ∷ xs) → Type}
      → p (x ⟨ InHere ⟩)
      → Σ[ y ∈ NameIn (x ∷ xs) ] p y
    lem1 h = _ , h
    {-# COMPILE AGDA2HS lem1 inline #-}

    lem2' : ∀ {@0 x xs} {p : @0 NameIn (x ∷ xs) → Type}
      → List (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
      → List (Σ[ y ∈ NameIn (x ∷ xs) ] p y)
    lem2' []             = []
    lem2' ((y , h) ∷ ys) = (mapRefine InThere y , h) ∷ lem2' ys
    {-# COMPILE AGDA2HS lem2' transparent #-}

    lem2 : ∀ {@0 x xs} {p : @0 NameIn (x ∷ xs) → Type}
      → NonEmpty (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
      → NonEmpty (Σ[ y ∈ NameIn (x ∷ xs) ] p y)
    lem2 ((y , h) ◂ ys) = (mapRefine InThere y , h) ◂ lem2' ys
    {-# COMPILE AGDA2HS lem2 transparent #-}

    @0 lem3 : ∀ {@0 x xs} {p : @0 NameIn (x ∷ xs) → Type}
      → Σ[ y ∈ NameIn (x ∷ xs) ] p y
      → Either
          (p (x ⟨ InHere ⟩))
          (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
    lem3 ((y ⟨ InHere ⟩)    , h') = Left h'
    lem3 ((y ⟨ InThere h ⟩) , h') = Right ((y ⟨ h ⟩) , h')

    @0 lem4 : ∀ {@0 x xs} {p : @0 NameIn (x ∷ xs) → Type}
      → NonEmpty (Σ[ y ∈ NameIn (x ∷ xs) ] p y)
      → These
          (p (x ⟨ InHere ⟩))
          (NonEmpty (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y)))
    lem4 = mapThese head id ∘ partitionEithersNonEmpty ∘ mapNonEmpty lem3

  decPAnyNameIn : (xs : List Name)
    → {@0 ys : List Name} (@0 eq : xs ≡ ys)
    → {p : @0 NameIn ys → Type}
    → (∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ _ ] p x))
  decPAnyNameIn []       refl f = No λ _ → undefined
  decPAnyNameIn (x ∷ xs) refl f =
    mapDecP
      (these (λ h → lem1 h ◂ []) lem2 (λ h hs → lem1 h ◂′ lem2 hs))
      lem4
      (theseDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl λ y → f (mapRefine InThere y)))
  {-# COMPILE AGDA2HS decPAnyNameIn #-}
