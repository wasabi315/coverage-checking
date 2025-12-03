open import CoverageCheck.Prelude
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_; _<|_)

module CoverageCheck.Name where

--------------------------------------------------------------------------------
-- Names and Scopes

Name : Type
Name = String
{-# COMPILE AGDA2HS Name #-}

-- Scope where names are unique
data Scope : Type
@0 Fresh : Name → Scope → Type

data Scope where
  SNil  : Scope
  SCons : (x : Name) (xs : Scope) → @0 Fresh x xs → Scope

pattern []        = SNil
pattern _∷#_ x xs = SCons x xs _
infixr 5 _∷#_

Fresh x []        = ⊤
Fresh x (y ∷# xs) = T (x /= y) × Fresh x xs

{-# COMPILE AGDA2HS Scope #-}

-- x is in scope
data In (x : Name) : Scope → Type where
  InHere  : ∀ {xs h} → In x (SCons x xs h)
  InThere : ∀ {y xs h} → In x xs → In x (SCons y xs h)

-- Name in scope
NameIn : @0 Scope → Type
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

--------------------------------------------------------------------------------
-- Eq/Ord instances for NameIn

-- x is fresh in xs implies x is not in xs
Fresh⇒¬In : ∀ {x} xs → Fresh x xs → ¬ In x xs
Fresh⇒¬In (SCons x xs h) (p , ps) InHere rewrite eqReflexivity x = explode p
Fresh⇒¬In (SCons x xs h) (p , ps) (InThere q) = Fresh⇒¬In xs ps q

-- Ins of the same type are always equal
In-unique : ∀ {x xs} (p q : In x xs) → p ≡ q
In-unique {xs = SCons _ _ _} InHere      InHere      = refl
In-unique {xs = SCons _ _ _} (InThere p) (InThere q) = cong InThere (In-unique p q)
In-unique {xs = SCons _ _ h} InHere      (InThere q) = explode (Fresh⇒¬In _ h q)
In-unique {xs = SCons _ _ h} (InThere p) InHere      = explode (Fresh⇒¬In _ h p)

-- Equality on the name parts enough to show that two NameIns are equal
NameIn≡ : ∀ {@0 xs} {x y : NameIn xs} → value x ≡ value y → x ≡ y
NameIn≡ {x = x ⟨ p ⟩} {y = x ⟨ q ⟩} refl = cong0 (x ⟨_⟩) (In-unique p q)

instance

  iEqNameIn : {@0 xs : Scope} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = value x == value y

  iLawfulEqNameIn : {@0 xs : Scope} → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y =
    mapReflects NameIn≡ (cong value) (isEquality (value x) (value y))

  iOrdFromLessThanNameIn : {@0 xs : Scope} → OrdFromLessThan (NameIn xs)
  iOrdFromLessThanNameIn .OrdFromLessThan._<_ x y = value x < value y

  iOrdNameIn : {@0 xs : Scope} → Ord (NameIn xs)
  iOrdNameIn = record {OrdFromLessThan iOrdFromLessThanNameIn}

--------------------------------------------------------------------------------
-- Universal set of names in scope

nameInSet' : ∀ xs {@0 ys}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → Set (NameIn ys)
nameInSet' [] inj = Set.empty
nameInSet' (x ∷# xs) inj =
  Set.insert (x ⟨ inj InHere ⟩) (nameInSet' xs (inj ∘ InThere))
{-# COMPILE AGDA2HS nameInSet' #-}

nameInSet : ∀ xs → Set (NameIn xs)
nameInSet xs = nameInSet' xs id
{-# COMPILE AGDA2HS nameInSet inline #-}

-- nameInSet is indeed universal

@0 nameInSet-universal' : ∀ xs {@0 ys}
  → (@0 inj : ∀ {@0 x} → In x xs → In x ys)
  → ((y ⟨ h ⟩) : NameIn xs)
  → Set.member (y ⟨ inj h ⟩) (nameInSet' xs inj) ≡ True
nameInSet-universal' (x ∷# xs) inj (x ⟨ InHere ⟩) =
  trans
    (prop-member-insert (x ⟨ inj InHere ⟩) (x ⟨ inj InHere ⟩) _)
    (cong (_|| Set.member (x ⟨ inj InHere ⟩)
      (nameInSet' xs (inj ∘ InThere))) (eqReflexivity x))
nameInSet-universal' (x ∷# xs) inj (y ⟨ InThere h ⟩) =
  trans
    (prop-member-insert (y ⟨ inj (InThere h) ⟩) (x ⟨ inj InHere ⟩) _)
    (trans
      (cong (y == x ||_) (nameInSet-universal' xs (inj ∘ InThere) (y ⟨ h ⟩)))
      (prop-x-||-True (y == x)))

@0 nameInSet-universal : ∀ xs x → Set.member x (nameInSet xs) ≡ True
nameInSet-universal xs = nameInSet-universal' xs id

--------------------------------------------------------------------------------
-- Any names in scope satisfy a given predicate?

-- Bool-returning version

anyNameIn' : ∀ {@0 xs} ys
  → (f : NameIn xs → Bool)
  → (@0 inj : ∀ {@0 x} → In x ys → In x xs)
  → Bool
anyNameIn' [] f inj = False
anyNameIn' (x ∷# ys) f inj =
  f (x ⟨ inj InHere ⟩) || anyNameIn' ys f (inj ∘ InThere)
{-# COMPILE AGDA2HS anyNameIn' #-}

anyNameIn : ∀ xs → (NameIn xs → Bool) → Bool
anyNameIn xs f = anyNameIn' xs f id
{-# COMPILE AGDA2HS anyNameIn inline #-}

-- Evidence-producing version

module _ {@0 xs} {p : @0 NameIn xs → Type} where

  foundHere : ∀ {y} {@0 ys h}
    → (@0 inj : ∀ {@0 x} → In x (SCons y ys h) → In x xs)
    → p (y ⟨ inj InHere ⟩)
    → NonEmpty (Σ[ x ∈ _ ] p (mapRefine inj x))
  foundHere inj p = NonEmpty.singleton (_ , p)
  {-# COMPILE AGDA2HS foundHere inline #-}

  foundThere' : ∀ {@0 y ys h}
    → (@0 inj : ∀ {@0 x} → In x (SCons y ys h) → In x xs)
    → List (Σ[ x ∈ _ ] p (mapRefine (inj ∘ InThere) x))
    → List (Σ[ x ∈ _ ] p (mapRefine inj x))
  foundThere' inj [] = []
  foundThere' inj ((x , p) ∷ ps) =
    (mapRefine InThere x , p) ∷ foundThere' inj ps
  {-# COMPILE AGDA2HS foundThere' transparent #-}

  foundThere : ∀ {@0 y ys h}
    → (@0 inj : ∀ {@0 x} → In x (SCons y ys h) → In x xs)
    → NonEmpty (Σ[ x ∈ _ ] p (mapRefine (inj ∘ InThere) x))
    → NonEmpty (Σ[ x ∈ _ ] p (mapRefine inj x))
  foundThere inj ((x , p) ∷ ps) = (mapRefine InThere x , p) ∷ foundThere' inj ps
  {-# COMPILE AGDA2HS foundThere transparent #-}

  @0 foundInv : ∀ {@0 y ys h}
    → (@0 inj : ∀ {@0 x} → In x (SCons y ys h) → In x xs)
    → Σ[ x ∈ _ ] p (mapRefine inj x)
    → These
        (p (y ⟨ inj InHere ⟩))
        (NonEmpty (Σ[ x ∈ _ ] p (mapRefine (inj ∘ InThere) x)))
  foundInv inj (x ⟨ InHere    ⟩ , p) = This p
  foundInv inj (x ⟨ InThere h ⟩ , p) = That ((x ⟨ h ⟩ , p) ∷ [])

  decPAnyNameIn' : ∀ ys
    → (f : ∀ x → DecP (p x))
    → (@0 inj : ∀ {@0 x} → In x ys → In x xs)
    → DecP (NonEmpty (Σ[ x ∈ _ ] p (mapRefine inj x)))
  decPAnyNameIn' [] f inj = No λ where (_ ∷ _) → undefined
  decPAnyNameIn' (SCons y ys h) f inj =
    mapDecP
      (bifoldMap1 (foundHere inj) (foundThere inj))
      (foundInv inj ∘ NonEmpty.head)
      (theseDecP
        (f (y ⟨ inj InHere ⟩))
        (decPAnyNameIn' ys f (inj ∘ InThere)))
  {-# COMPILE AGDA2HS decPAnyNameIn' #-}

-- Decides whether any names in scope satisfy a given predicate
-- If yes, this function returns a non-empty list of NameIn
-- together with the proof that the predicate is indeed satisfied
decPAnyNameIn : ∀ xs {@0 ys}
  → (@0 eq : xs ≡ ys)
  → {p : @0 NameIn ys → Type}
  → (∀ x → DecP (p x))
  → DecP (NonEmpty (Σ[ x ∈ NameIn ys ] p x))
decPAnyNameIn xs refl f = decPAnyNameIn' xs f id
{-# COMPILE AGDA2HS decPAnyNameIn #-}
