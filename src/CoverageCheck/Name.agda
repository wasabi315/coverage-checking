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

data In (x : Name) : Scope → Type where
  InHere  : ∀ {xs h} → In x (SCons x xs h)
  InThere : ∀ {y xs h} → In x xs → In x (SCons y xs h)

NameIn : @0 Scope → Type
NameIn xs = ∃[ x ∈ Name ] In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

--------------------------------------------------------------------------------
-- Eq/Ord instances

Fresh⇒¬In : ∀ {x} xs → Fresh x xs → ¬ In x xs
Fresh⇒¬In (SCons x xs h) (p , ps) InHere rewrite eqReflexivity x = explode p
Fresh⇒¬In (SCons x xs h) (p , ps) (InThere q) = Fresh⇒¬In xs ps q

In-unique : ∀ {x xs} (p q : In x xs) → p ≡ q
In-unique {xs = SCons _ _ _} InHere      InHere      = refl
In-unique {xs = SCons _ _ _} (InThere p) (InThere q) = cong InThere (In-unique p q)
In-unique {xs = SCons _ _ h} InHere      (InThere q) = explode (Fresh⇒¬In _ h q)
In-unique {xs = SCons _ _ h} (InThere p) InHere      = explode (Fresh⇒¬In _ h p)

NameIn≡ : ∀ {@0 xs} {x y : NameIn xs} → value x ≡ value y → x ≡ y
NameIn≡ {x = x ⟨ p ⟩} {y = y ⟨ q ⟩} refl = cong0 (x ⟨_⟩) (In-unique p q)

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
-- Universal set

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
-- Properties

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

module _ where
  private
    lem1 : ∀ {x} {@0 xs h} {p : @0 NameIn (SCons x xs h) → Type}
      → p (x ⟨ InHere ⟩)
      → Σ[ y ∈ NameIn (SCons x xs h) ] p y
    lem1 h = _ , h
    {-# COMPILE AGDA2HS lem1 inline #-}

    lem2' : ∀ {@0 x xs h} {p : @0 NameIn (SCons x xs h) → Type}
      → List (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
      → List (Σ[ y ∈ NameIn (SCons x xs h) ] p y)
    lem2' []             = []
    lem2' ((y , h) ∷ ys) = (mapRefine InThere y , h) ∷ lem2' ys
    {-# COMPILE AGDA2HS lem2' transparent #-}

    lem2 : ∀ {@0 x xs h} {p : @0 NameIn (SCons x xs h) → Type}
      → NonEmpty (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
      → NonEmpty (Σ[ y ∈ NameIn (SCons x xs h) ] p y)
    lem2 ((y , h) ∷ ys) = (mapRefine InThere y , h) ∷ lem2' ys
    {-# COMPILE AGDA2HS lem2 transparent #-}

    @0 lem3 : ∀ {@0 x xs h} {p : @0 NameIn (SCons x xs h) → Type}
      → Σ[ y ∈ NameIn (SCons x xs h) ] p y
      → Either
          (p (x ⟨ InHere ⟩))
          (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y))
    lem3 ((y ⟨ InHere ⟩)    , h') = Left h'
    lem3 ((y ⟨ InThere h ⟩) , h') = Right ((y ⟨ h ⟩) , h')

    @0 lem4 : ∀ {@0 x xs h} {p : @0 NameIn (SCons x xs h) → Type}
      → NonEmpty (Σ[ y ∈ NameIn (SCons x xs h) ] p y)
      → These
          (p (x ⟨ InHere ⟩))
          (NonEmpty (Σ[ y ∈ NameIn xs ] p (mapRefine InThere y)))
    lem4 = mapThese NonEmpty.head id ∘ partitionEithersNonEmpty ∘ fmap lem3

  decPAnyNameIn : ∀ xs {@0 ys}
    → (@0 eq : xs ≡ ys)
    → {p : @0 NameIn ys → Type}
    → (∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ _ ] p x))
  decPAnyNameIn []       refl f = No λ where (_ ∷ _) → undefined
  decPAnyNameIn (x ∷# xs) refl f =
    mapDecP
      (these (λ h → lem1 h ∷ []) lem2 (λ h hs → lem1 h <| lem2 hs))
      lem4
      (theseDecP (f (x ⟨ InHere ⟩)) (decPAnyNameIn xs refl λ y → f (mapRefine InThere y)))
  {-# COMPILE AGDA2HS decPAnyNameIn #-}
