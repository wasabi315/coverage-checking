open import CoverageCheck.Prelude
open import CoverageCheck.Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _<|_)
open import Haskell.Law.Eq.Instances

module CoverageCheck.Name where

--------------------------------------------------------------------------------
-- Names and Scopes

Name = String
{-# COMPILE AGDA2HS Name #-}

Scope : Type
Scope = List (Erase Name)
{-# COMPILE AGDA2HS Scope #-}

-- Name in scope
-- compiles to Natural
NameIn : @0 Scope → Type
NameIn xs = Σ0 _ λ x → In x xs
{-# COMPILE AGDA2HS NameIn inline #-}

--------------------------------------------------------------------------------
-- Eq/Ord instances for NameIn

@0 NameIn≡ : {@0 xs : Scope}
  {u@(⟨ x ⟩ (m ⟨ p ⟩)) v@(⟨ y ⟩ (n ⟨ q ⟩)) : NameIn xs}
  → m ≡ n
  → u ≡ v
NameIn≡ {u = ⟨ x ⟩ m} {⟨ y ⟩ n} eq
  with refl , refl ← In≡ m n eq
  = refl

instance

  iEqNameIn : {@0 xs : Scope} → Eq (NameIn xs)
  iEqNameIn ._==_ (⟨ _ ⟩ (m ⟨ _ ⟩)) (⟨ _ ⟩ (n ⟨ _ ⟩)) = m == n

  @0 iLawfulEqNameIn : {@0 xs : Scope} → IsLawfulEq (NameIn xs)
  iLawfulEqNameIn .IsLawfulEq.isEquality (⟨ x ⟩ (m ⟨ p ⟩)) (⟨ y ⟩ (n ⟨ q ⟩)) =
    mapReflects {a = m ≡ n}
      NameIn≡ (cong λ (⟨ _ ⟩ (o ⟨ _ ⟩)) → o)
      (isEquality m n)

  iOrdFromLessThanNameIn : {@0 xs : Scope} → OrdFromLessThan (NameIn xs)
  iOrdFromLessThanNameIn .OrdFromLessThan.super = iEqNameIn
  iOrdFromLessThanNameIn .OrdFromLessThan._<_ (⟨ _ ⟩ (m ⟨ _ ⟩)) (⟨ _ ⟩ (n ⟨ _ ⟩)) = m < n

  iOrdNameIn : {@0 xs : Scope} → Ord (NameIn xs)
  iOrdNameIn = record {OrdFromLessThan iOrdFromLessThanNameIn}

--------------------------------------------------------------------------------
-- Renaming

Ren : (@0 xs ys : Scope) → Type
Ren xs ys = ∀ {@0 x} → In x xs → In x ys
{-# COMPILE AGDA2HS Ren inline #-}

rename : ∀ {@0 xs ys} → Ren xs ys → NameIn xs → NameIn ys
rename ren (⟨ x ⟩ p) = ⟨ x ⟩ ren p
{-# COMPILE AGDA2HS rename #-}

--------------------------------------------------------------------------------
-- Universal set of names in scope

nameInSet' : ∀ xs {@0 ys}
  → Ren xs ys
  → Set (NameIn ys)
nameInSet' [] ren = Set.empty
nameInSet' (x ∷ xs) ren = Set.insert (rename ren (⟨ x ⟩ inHere)) (nameInSet' xs (ren ∘ inThere))
{-# COMPILE AGDA2HS nameInSet' #-}

nameInSet : ∀ xs → Set (NameIn xs)
nameInSet xs = nameInSet' xs id
{-# COMPILE AGDA2HS nameInSet #-}

-- nameInSet is indeed universal

@0 nameInSet-universal' : ∀ xs {@0 ys}
  → (ren : Ren xs ys)
  → (x : NameIn xs)
  → Set.member (rename ren x) (nameInSet' xs ren) ≡ True
nameInSet-universal' [] ren (⟨ _ ⟩ p) = explode (¬In[] p)
nameInSet-universal' (x ∷ xs) ren (⟨ x ⟩ (zero ⟨ isZero refl ⟩)) =
  trans
    (Set.prop-member-insert _ _ _)
    (cong
      (_|| Set.member (rename ren (⟨ x ⟩ inHere)) (nameInSet' xs (ren ∘ inThere)))
      (eqReflexivity (rename ren (⟨ x ⟩ inHere))))
nameInSet-universal' (x ∷ xs) ren (⟨ y ⟩ (suc n ⟨ isSuc p ⟩)) =
  trans
    (Set.prop-member-insert _ _ _)
    (trans
      (cong (rename ren (⟨ y ⟩ InThere n p) == rename ren (⟨ x ⟩ inHere) ||_)
        (nameInSet-universal' xs (ren ∘ inThere) (⟨ y ⟩ (n ⟨ p ⟩))))
      (prop-x-||-True (rename ren (⟨ y ⟩ InThere n p) == rename ren (⟨ x ⟩ inHere))))


@0 nameInSet-universal : ∀ xs x → Set.member x (nameInSet xs) ≡ True
nameInSet-universal xs = nameInSet-universal' xs id

--------------------------------------------------------------------------------
-- Any names in scope satisfy a given predicate?

-- Bool-returning version

anyNameIn' : ∀ {@0 xs} ys
  → (@0 ren : Ren ys xs)
  → (f : NameIn ys → Bool)
  → Bool
anyNameIn' [] ren f = False
anyNameIn' (x ∷ ys) ren f =
  f (⟨ x ⟩ inHere) || anyNameIn' ys (ren ∘ inThere) (f ∘ (rename inThere))
{-# COMPILE AGDA2HS anyNameIn' #-}

anyNameIn : ∀ xs → (NameIn xs → Bool) → Bool
anyNameIn xs f = anyNameIn' xs id f
{-# COMPILE AGDA2HS anyNameIn #-}

-- Evidence-producing version

module _ {@0 xs} {p : @0 NameIn xs → Type} where

  foundHere : ∀ {y} {@0 ys}
    → (@0 ren : Ren (y ∷ ys) xs)
    → p (rename ren (⟨ y ⟩ inHere))
    → NonEmpty (Σ[ x ∈ _ ] p (rename ren x))
  foundHere sh p = NonEmpty.singleton (_ , p)
  {-# COMPILE AGDA2HS foundHere inline #-}

  foundThere' : ∀ {@0 y ys}
    → (@0 ren : Ren (y ∷ ys) xs)
    → List (Σ[ x ∈ _ ] p (rename (ren ∘ inThere) x))
    → List (Σ[ x ∈ _ ] p (rename ren x))
  foundThere' ren [] = []
  foundThere' ren ((x , p) ∷ ps) = (rename inThere x , p) ∷ foundThere' ren ps
  {-# COMPILE AGDA2HS foundThere' #-}

  foundThere : ∀ {@0 y ys}
    → (@0 ren : Ren (y ∷ ys) xs)
    → NonEmpty (Σ[ x ∈ _ ] p (rename (ren ∘ inThere) x))
    → NonEmpty (Σ[ x ∈ _ ] p (rename ren x))
  foundThere ren ((x , p) ∷ ps) = (rename inThere x , p) ∷ foundThere' ren ps
  {-# COMPILE AGDA2HS foundThere #-}

  foundInv : ∀ {@0 y ys}
    → (@0 ren : Ren (y ∷ ys) xs)
    → Σ[ x ∈ _ ] p (rename ren x)
    → Either
        (p (rename ren (⟨ y ⟩ inHere)))
        (NonEmpty (Σ[ x ∈ _ ] p (rename (ren ∘ inThere) x)))
  foundInv ren (⟨ x ⟩ InHere , q)      = Left q
  foundInv ren (⟨ x ⟩ InThere n p , q) = Right ((⟨ x ⟩ (n ⟨ p ⟩) , q) ∷ [])

  decPAnyNameIn' : ∀ ys
    → (ren : Ren ys xs)
    → (f : ∀ x → DecP (p x))
    → DecP (NonEmpty (Σ[ x ∈ _ ] p (rename ren x)))
  decPAnyNameIn' [] ren f = No λ where ((⟨ _ ⟩ p , _) ∷ _) → ¬In[] p
  decPAnyNameIn' (y ∷ ys) ren f =
    mapDecP
      (bifoldMap1 (foundHere ren) (foundThere ren))
      (eitherToThese ∘ foundInv ren ∘ NonEmpty.head)
      (theseDecP
        (f (rename ren (⟨ y ⟩ inHere)))
        (decPAnyNameIn' ys (ren ∘ inThere) f))
  {-# COMPILE AGDA2HS decPAnyNameIn' #-}


-- Decides whether any name in scope satisfies a given predicate
-- If yes, this function returns a non-empty list of NameIn
-- together with the proof that the predicate is indeed satisfied
decPAnyNameIn : ∀ xs {@0 ys}
  → (@0 eq : xs ≡ ys)
  → {p : @0 NameIn ys → Type}
  → (∀ x → DecP (p x))
  → DecP (NonEmpty (Σ[ x ∈ _ ] p x))
decPAnyNameIn xs refl f = decPAnyNameIn' xs id f
{-# COMPILE AGDA2HS decPAnyNameIn #-}

-- Boolean-returning version on Haskell side

module _ {@0 xs} {@0 p : @0 NameIn xs → Type} where

  decAnyNameIn' : ∀ ys
    → (ren : Ren ys xs)
    → (f : ∀ x → Dec (p x))
    → Dec (NonEmpty (Σ[ x ∈ _ ] p (rename ren x)))
  decAnyNameIn' [] ren f = False ⟨ (λ where ((⟨ _ ⟩ p , _) ∷ _) → ¬In[] p) ⟩
  decAnyNameIn' (y ∷ ys) ren f =
    mapDec
      (bifoldMap1 (foundHere {p = p} ren) (foundThere {p = p} ren))
      (foundInv {p = p} ren ∘ NonEmpty.head)
      (eitherDec
        (f (rename ren (⟨ y ⟩ inHere)))
        (decAnyNameIn' ys (ren ∘ inThere) f))
  {-# COMPILE AGDA2HS decAnyNameIn' #-}


decAnyNameIn : ∀ xs {@0 ys}
  → (@0 eq : xs ≡ ys)
  → {@0 p : @0 NameIn ys → Type}
  → (∀ x → Dec (p x))
  → Dec (NonEmpty (Σ[ x ∈ NameIn ys ] p x))
decAnyNameIn xs refl f = decAnyNameIn' xs id f
{-# COMPILE AGDA2HS decAnyNameIn #-}
