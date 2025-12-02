open import CoverageCheck.Prelude
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_; _<|_)

module CoverageCheck.Name where

--------------------------------------------------------------------------------

Name : Type
Name = String
{-# COMPILE AGDA2HS Name #-}

NameIn : @0 List Name → Type
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

--------------------------------------------------------------------------------

NameIn≡ : ∀ {@0 xs} ⦃ @0 _ : Fresh xs ⦄ {x y : NameIn xs}
  → value x ≡ value y
  → x ≡ y
NameIn≡ {xs} ⦃ h ⦄ {x ⟨ p ⟩} {y ⟨ q ⟩} refl
  = cong0 (x ⟨_⟩) (fresh⇒uniqueIn x xs h p q)

instance
  -- import instances
  open import Haskell.Prim.Eq using ()
  open import Haskell.Law.Eq using ()
  open import Haskell.Prim.Ord using (_<_)

  iEqNameIn : {@0 xs : List Name} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = value x == value y

  iLawfulEqNameIn : {@0 xs : List Name} ⦃ @0 _ : Fresh xs ⦄ → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y
    = mapReflects NameIn≡ (cong value) (isEquality (value x) (value y))

  iOrdFromLessThanNameIn : {@0 xs : List Name} → OrdFromLessThan (NameIn xs)
  iOrdFromLessThanNameIn .OrdFromLessThan._<_ x y = value x < value y

  iOrdNameIn : {@0 xs : List Name} → Ord (NameIn xs)
  iOrdNameIn = record {OrdFromLessThan iOrdFromLessThanNameIn}

--------------------------------------------------------------------------------

allNameIn' : (xs : List Name) {@0 ys : List Name}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → List (NameIn ys)
allNameIn' []       inj = []
allNameIn' (x ∷ xs) inj =
  (x ⟨ inj InHere ⟩) ∷ allNameIn' xs (inj ∘ InThere)
{-# COMPILE AGDA2HS allNameIn' transparent #-}

allNameIn : (xs : List Name) → List (NameIn xs)
allNameIn xs = allNameIn' xs id
{-# COMPILE AGDA2HS allNameIn inline #-}

@0 allNameIn-universal' : (xs : List Name) {@0 ys : List Name}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → ∀ ((y ⟨ h ⟩) : NameIn xs)
  → elem (y ⟨ inj h ⟩) (allNameIn' xs inj) ≡ True
allNameIn-universal' (x ∷ xs) inj (y ⟨ InHere ⟩) rewrite eqReflexivity x = refl
allNameIn-universal' (x ∷ xs) inj (y ⟨ InThere h ⟩) =
  let ih = allNameIn-universal' xs (inj ∘ InThere) (y ⟨ h ⟩) in
  subst (λ b → (y == x || b) ≡ True) (sym ih) (prop-x-||-True (y == x))

@0 allNameIn-universal : (xs : List Name)
  → ∀ x → elem x (allNameIn xs) ≡ True
allNameIn-universal xs x = allNameIn-universal' xs id x

allNameInSet : (xs : List Name) → Set (NameIn xs)
allNameInSet xs = Set.fromList (allNameIn xs)
{-# COMPILE AGDA2HS allNameInSet inline #-}

@0 allNameInSet-universal : (xs : List Name)
  → ∀ x → Set.member x (allNameInSet xs) ≡ True
allNameInSet-universal xs x rewrite prop-member-fromList x (allNameIn xs)
  = allNameIn-universal xs x

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
    lem2 ((y , h) ∷ ys) = (mapRefine InThere y , h) ∷ lem2' ys
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
    lem4 = mapThese NonEmpty.head id ∘ partitionEithersNonEmpty ∘ fmap lem3

  decPAnyNameIn : (xs : List Name)
    → {@0 ys : List Name} (@0 eq : xs ≡ ys)
    → {p : @0 NameIn ys → Type}
    → (∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ _ ] p x))
  decPAnyNameIn []       refl f = No λ where (x ∷ _) → undefined
  decPAnyNameIn (x ∷ xs) refl f =
    mapDecP
      (these (λ h → lem1 h ∷ []) lem2 (λ h hs → lem1 h <| lem2 hs))
      lem4
      (theseDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl λ y → f (mapRefine InThere y)))
  {-# COMPILE AGDA2HS decPAnyNameIn #-}
