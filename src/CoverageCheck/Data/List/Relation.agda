module CoverageCheck.Data.List.Relation where

open import Haskell.Prelude hiding (All; Any; a; b; e)
open import Haskell.Data.Bifunctor
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Extra.Nat
open import Haskell.Extra.Sigma
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq
open import Haskell.Law.Eq.Instances
open import Haskell.Law.Equality

open import CoverageCheck.Extra.Negation
open import CoverageCheck.Extra.DecP

private
  variable
    @0 e e' : Type
    a b : @0 e → Type
    @0 x y : e
    @0 xs ys : List e
    n : Nat

infixr 5 _∷_

--------------------------------------------------------------------------------
-- Membership

data IsNth (@0 x : e) : (@0 xs : List e) → Nat → Type where
  isZero : x ≡ y → IsNth x (y ∷ xs) zero
  isSuc  : IsNth x xs n → IsNth x (y ∷ xs) (suc n)

-- compiles to Natural
In : (@0 x : e) (@0 xs : List e) → Type
In x xs = ∃ Nat λ n → IsNth x xs n
{-# COMPILE AGDA2HS In inline #-}

pattern InHere = zero ⟨ isZero refl ⟩
inHere : In x (x ∷ xs)
inHere = InHere
{-# COMPILE AGDA2HS inHere inline #-}

pattern InThere n h = suc n ⟨ isSuc h ⟩
inThere : In x xs → In x (y ∷ xs)
inThere (n ⟨ h ⟩) = InThere n h
{-# COMPILE AGDA2HS inThere #-}

¬In[] : {@0 x : e} → ¬ In x []
¬In[] _ = undefined

@0 IsNth-unique : {@0 xs : List e} {@0 x y : e}
  → (p : IsNth x xs n) (q : IsNth y xs n)
  → Σ (x ≡ y) λ where refl → p ≡ q
IsNth-unique (isZero refl) (isZero refl) = refl , refl
IsNth-unique (isSuc p) (isSuc q)
  with refl , refl ← IsNth-unique p q
  = refl , refl

@0 In≡ : {@0 xs : List e} {@0 x y : e}
  → (p : In x xs) (q : In y xs)
  → p .value ≡ q .value
  → Σ (x ≡ y) λ where refl → p ≡ q
In≡ p q refl
  with refl , refl ← IsNth-unique (p .proof) (q .proof)
  = refl , refl

--------------------------------------------------------------------------------
-- All

data All (a : @0 e → Type) : (@0 xs : List e) → Type where
  []  : All a []
  _∷_ : a x → All a xs → All a (x ∷ xs)
{-# COMPILE AGDA2HS All to List #-}

headAll : All a (x ∷ xs) → a x
headAll (x ∷ _) = x
{-# COMPILE AGDA2HS headAll to head #-}

tailAll : All a (x ∷ xs) → All a xs
tailAll (_ ∷ xs) = xs
{-# COMPILE AGDA2HS tailAll to tail #-}

mapAll : (∀ {@0 x} → a x → b x) → (∀ {@0 xs} → All a xs → All b xs)
mapAll f [] = []
mapAll f (x ∷ xs) = f x ∷ mapAll f xs

--------------------------------------------------------------------------------
-- Any

data Any (a : @0 e → Type) : (@0 xs : List e) → Type where
  Here  : a x → Any a (x ∷ xs)
  There : Any a xs → Any a (y ∷ xs)
{-# COMPILE AGDA2HS Any deriving (Show, Eq, Ord) #-}

¬Any[] : ¬ Any a []
¬Any[] ()

anyToEither : Any a (x ∷ xs) → Either (a x) (Any a xs)
anyToEither (Here  p) = Left p
anyToEither (There p) = Right p

--------------------------------------------------------------------------------
-- First

data First (a : @0 e → Type) : (@0 xs : List e) → Type where
  FHere  : a x → First a (x ∷ xs)
  FThere : @0 ¬ a y → First a xs → First a (y ∷ xs)
{-# COMPILE AGDA2HS First deriving (Show, Eq, Ord) #-}

tailFirst : ¬ a x → First a (x ∷ xs) → First a xs
tailFirst ¬p (FHere p)    = contradiction p ¬p
tailFirst ¬p (FThere _ p) = p

¬First[] : ¬ First a []
¬First[] ()

firstDecP : ∀ {e} {a : @0 e → Type}
  → (∀ x → DecP (a x))
  → ∀ xs → DecP (First a xs)
firstDecP f [] = No ¬First[]
firstDecP f (x ∷ xs) = ifDecP (f x)
  (λ ⦃ p ⦄ → Yes (FHere p))
  (λ ⦃ ¬p ⦄ → mapDecP (FThere ¬p) (tailFirst ¬p) (firstDecP f xs))
{-# COMPILE AGDA2HS firstDecP #-}

--------------------------------------------------------------------------------
-- Some & Many

data Many (a : @0 e → Type) : (@0 xs : List e) → Type where
  MNil   : Many a []
  MHere  : a x → Many a xs → Many a (x ∷ xs)
  MThere : Many a xs → Many a (x ∷ xs)

{-# COMPILE AGDA2HS Many deriving (Eq, Show) #-}

tailMany : ∀ {@0 x xs} → Many a (x ∷ xs) → Many a xs
tailMany (MHere _ xs) = xs
tailMany (MThere xs)  = xs
{-# COMPILE AGDA2HS tailMany #-}

trivialMany : ∀ xs → Many a xs
trivialMany []       = MNil
trivialMany (_ ∷ xs) = MThere (trivialMany xs)

manyDecP : {e : Type} {a : @0 e → Type}
  → (∀ x → DecP (a x))
  → ∀ xs → DecP (Many a xs)
manyDecP f [] = Yes MNil
manyDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (MHere px) tailMany (manyDecP f xs))
    (mapDecP MThere tailMany (manyDecP f xs))
{-# COMPILE AGDA2HS manyDecP #-}

data Some (a : @0 e → Type) : (@0 xs : List e) → Type where
  SHere  : a x → Many a xs → Some a (x ∷ xs)
  SThere : Some a xs → Some a (x ∷ xs)

{-# COMPILE AGDA2HS Some deriving (Eq, Show) #-}

someToMany : ∀ {@0 xs} → Some a xs → Many a xs
someToMany (SHere x xs) = MHere x xs
someToMany (SThere xs)  = MThere (someToMany xs)
{-# COMPILE AGDA2HS someToMany #-}

tailSome : ∀ {@0 x xs} → Some a (x ∷ xs) → Many a xs
tailSome (SHere x xs) = xs
tailSome (SThere xs)  = someToMany xs
{-# COMPILE AGDA2HS tailSome #-}

unthereSome : @0 ¬ a x → Some a (x ∷ xs) → Some a xs
unthereSome ¬px (SHere x xs) = contradiction x ¬px
unthereSome ¬px (SThere xs)  = xs
{-# COMPILE AGDA2HS unthereSome #-}

someDecP : {e : Type} {a : @0 e → Type}
  → (∀ x → DecP (a x))
  → ∀ xs → DecP (Some a xs)
someDecP f [] = No λ _ → undefined
someDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (SHere px) tailSome (manyDecP f xs))
    (λ ⦃ ¬px ⦄ → mapDecP SThere (unthereSome ¬px) (someDecP f xs))
{-# COMPILE AGDA2HS someDecP #-}

--------------------------------------------------------------------------------

data HPointwise
  {@0 e : Type} {@0 p q : @0 e → Type}
  (a : ∀ {@0 x} → @0 p x → @0 q x → Type)
  : ∀ {@0 xs} → @0 All p xs → @0 All q xs → Type
  where
  []  : HPointwise a [] []
  _∷_ : ∀ {@0 x xs}
    → {@0 px : p x} {@0 pxs : All p xs}
    → {@0 qx : q x} {@0 qxs : All q xs}
    → a px qx
    → HPointwise a pxs qxs
    → HPointwise a (px ∷ pxs) (qx ∷ qxs)

{-# COMPILE AGDA2HS HPointwise to List #-}

--------------------------------------------------------------------------------

All¬⇒¬Any : All (λ x → ¬ a x) xs → ¬ Any a xs
All¬⇒¬Any []       _         = undefined
All¬⇒¬Any (x ∷ xs) (Here p)  = x p
All¬⇒¬Any (x ∷ xs) (There p) = All¬⇒¬Any xs p

¬Any⇒All¬ : ∀ xs → ¬ Any a xs → All (λ x → ¬ a x) xs
¬Any⇒All¬ []       ¬p = []
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ Here ∷ ¬Any⇒All¬ xs (¬p ∘ There)

First⇒Any : First a xs → Any a xs
First⇒Any (FHere p)    = Here p
First⇒Any (FThere _ p) = There (First⇒Any p)

¬First⇒¬Any : ¬ First a xs → ¬ Any a xs
¬First⇒¬Any ¬p (Here p)  = ¬p (FHere p)
¬First⇒¬Any ¬p (There p) = ¬First⇒¬Any (¬p ∘ FThere (¬p ∘ FHere)) p

gmapAny⁺ : {@0 f : e → e'}
  → (∀ {@0 x} → a x → b (f x))
  → Any a xs → Any b (map f xs)
gmapAny⁺ g (Here p)  = Here (g p)
gmapAny⁺ g (There p) = There (gmapAny⁺ g p)

++Any⁺ˡ : Any a xs → Any a (xs ++ ys)
++Any⁺ˡ (Here p)  = Here p
++Any⁺ˡ (There p) = There (++Any⁺ˡ p)

++Any⁺ʳ : ∀ {xs} {@0 ys} → Any a ys → Any a (xs ++ ys)
++Any⁺ʳ {xs = []}     p = p
++Any⁺ʳ {xs = x ∷ xs} p = There (++Any⁺ʳ p)

@0 gconcatMapAny⁺ : {@0 f : e → List e'}
  → (∀ {@0 x} → a x → Any b (f x))
  → Any a xs → Any b (concatMap f xs)
gconcatMapAny⁺ g (Here p)  = ++Any⁺ˡ (g p)
gconcatMapAny⁺ g (There p) = ++Any⁺ʳ (gconcatMapAny⁺ g p)

++Any⁻ : ∀ xs {@0 ys} → Any a (xs ++ ys) → Either (Any a xs) (Any a ys)
++Any⁻ []       p         = Right p
++Any⁻ (x ∷ xs) (Here p)  = Left (Here p)
++Any⁻ (x ∷ xs) (There p) = bimap There id (++Any⁻ xs p)

gmapAny⁻ : {@0 f : e → e'}
  → (∀ {x} → b (f x) → a x)
  → ∀ {xs} → Any b (map f xs) → Any a xs
gmapAny⁻ g {x ∷ xs} (Here p)  = Here (g p)
gmapAny⁻ g {x ∷ xs} (There p) = There (gmapAny⁻ g p)

gconcatMapAny⁻ : {f : e → List e'}
  → (∀ {x} → Any b (f x) → a x)
  → ∀ {xs} → Any b (concatMap f xs) → Any a xs
gconcatMapAny⁻ {f = f} g {x ∷ xs} p with ++Any⁻ (f x) p
... | Left q  = Here (g q)
... | Right q = There (gconcatMapAny⁻ g q)

¬Some⇒All¬ : ∀ xs → ¬ Some a xs → All (λ x → ¬ a x) xs
¬Some⇒All¬ [] _ = []
¬Some⇒All¬ (x ∷ xs) ¬pxxs =
  (λ px → ¬pxxs (SHere px (trivialMany xs))) ∷ ¬Some⇒All¬ xs (¬pxxs ∘ SThere)
