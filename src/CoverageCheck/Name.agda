open import CoverageCheck.Prelude

module CoverageCheck.Name where

--------------------------------------------------------------------------------

Name : Set
Name = String
{-# COMPILE AGDA2HS Name inline #-}

data In (x : Name) : (xs : List Name) → Set where
  InHere  : ∀ {xs} → In x (x ∷ xs)
  InThere : ∀ {y xs} → In x xs → In x (y ∷ xs)

record NameIn (@0 xs : List Name) : Set where
  constructor _⟨_⟩
  field
    name       : Name
    @0 .inName : In name xs
{-# COMPILE AGDA2HS NameIn unboxed #-}

open NameIn public

name-injective : {@0 xs : List Name} {x y : NameIn xs} → name x ≡ name y → x ≡ y
name-injective refl = refl

instance
  -- import instances
  open import Haskell.Prim.Eq using ()
  open import Haskell.Law.Eq using ()

  iEqNameIn : {@0 xs : List Name} → Eq (NameIn xs)
  iEqNameIn ._==_ x y = name x == name y

  iLawfulEqNameIn : {@0 xs : List Name} → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .isEquality x y
    = mapReflects name-injective (cong name) (isEquality (name x) (name y))
