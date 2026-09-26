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

invIsZero :
  {@0 n : Nat} →
  @0 IsNth x xs n →
  @0 n ≡ 0 →
  (f : (@0 xs : List e) → Type) →
  (∀ {@0 ys} → f (x ∷ ys)) →
  f xs
invIsZero {n = _} (isZero refl) refl _ x = x
{-# COMPILE AGDA2HS invIsZero transparent #-}

invIsSuc :
  @0 IsNth x xs n →
  @0 ¬ n ≡ 0 →
  (f : (@0 xs : List e) (@0 n : Nat) → Type) →
  (∀ m {@0 y ys} → @0 n ≡ suc m → @0 IsNth x ys m → f (y ∷ ys) n) →
  f xs n
wInvIsSuc :
  {@0 n : Nat} →
  @0 IsNth x xs n →
  (∃ Nat λ m → n ≡ suc m) →
  (f : (@0 xs : List e) (@0 n : Nat) → Type) →
  (∀ m {@0 y ys} → @0 n ≡ suc m → @0 IsNth x ys m → f (y ∷ ys) n) →
  f xs n
invIsSuc p q f g = wInvIsSuc p (predNat _ q) f g
wInvIsSuc (isSuc p) (m ⟨ refl ⟩) f g = g m refl p
{-# COMPILE AGDA2HS invIsSuc inline #-}
{-# COMPILE AGDA2HS wInvIsSuc #-}

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

-- compiles to (Natural, a)
Any : (a : @0 e → Type) (@0 xs : List e) → Type
Any a xs = Σ0 _ λ x → Σ (In x xs) λ _ → a x
{-# COMPILE AGDA2HS Any #-}

pattern Here {x} h = ⟨ x ⟩ (InHere , h)
here : a x → Any a (x ∷ xs)
here x = Here x
{-# COMPILE AGDA2HS here inline #-}

pattern There {x} n h h' = ⟨ x ⟩ (InThere n h , h')
there : Any a xs → Any a (x ∷ xs)
there = λ where (< n ⟨ h ⟩ , h' >) → There n h h'
{-# COMPILE AGDA2HS there inline #-}

¬Any[] : ¬ Any a []
¬Any[] _ = undefined

anyToEither : Any a (x ∷ xs) → Either (a x) (Any a xs)
anyToEither (< InHere      , q >) = Left q
anyToEither (< InThere n p , q >) = Right < n ⟨ p ⟩ , q >

module _
  (f : (@0 xs : List e) → Type)
  (h : ∀ {@0 x xs} → a x → f (x ∷ xs))
  (t : ∀ {@0 x xs} → f xs → f (x ∷ xs))
  where

  wRecAny : (n : Nat) → @0 IsNth x xs n → a x → f xs
  wRecAny n p q =
    ifDec (n ≟ 0)
      (λ ⦃ r ⦄ →
        invIsZero p r (λ ys → f ys) (h q))
      (λ ⦃ r ⦄ →
        invIsSuc p r (λ ys _ → f ys) λ where n refl p → t (wRecAny n p q))
  {-# COMPILE AGDA2HS wRecAny #-}

  recAny : Any a xs → f xs
  recAny (⟨ _ ⟩ (n ⟨ p ⟩ , q)) = wRecAny n p q
  {-# COMPILE AGDA2HS recAny inline #-}

--------------------------------------------------------------------------------
-- First

data FirstWitness (a : @0 e → Type) (@0 x : e) : (@0 xs : List e) → Nat → Type where
  isZero : x ≡ y → FirstWitness a x (y ∷ xs) zero
  isSuc  : @0 ¬ a y → FirstWitness a x xs n → FirstWitness a x (y ∷ xs) (suc n)

invIsZeroF :
  {@0 n : Nat} →
  @0 FirstWitness a x xs n →
  @0 n ≡ 0 →
  (f : (@0 xs : List e) → Type) →
  (∀ {@0 ys} → f (x ∷ ys)) →
  f xs
invIsZeroF (isZero refl) refl _ x = x
{-# COMPILE AGDA2HS invIsZeroF transparent #-}

invIsSucF :
  @0 FirstWitness a x xs n →
  @0 ¬ n ≡ 0 →
  (f : (@0 xs : List e) (@0 n : Nat) → Type) →
  (∀ m {@0 y ys} → @0 n ≡ suc m → @0 ¬ a y → @0 FirstWitness a x ys m → f (y ∷ ys) n) →
  f xs n
wInvIsSucF :
  {@0 n : Nat} →
  @0 FirstWitness a x xs n →
  (∃ Nat λ m → n ≡ suc m) →
  (f : (@0 xs : List e) (@0 n : Nat) → Type) →
  (∀ m {@0 y ys} → @0 n ≡ suc m → @0 ¬ a y → @0 FirstWitness a x ys m → f (y ∷ ys) n) →
  f xs n
invIsSucF p q f g = wInvIsSucF p (predNat _ q) f g
wInvIsSucF (isSuc p q) (m ⟨ refl ⟩) f g = g m refl p q
{-# COMPILE AGDA2HS invIsSucF inline #-}
{-# COMPILE AGDA2HS wInvIsSucF #-}

-- compiles to (Natural, a)
First : (a : @0 e → Type) (@0 xs : List e) → Type
First a xs = Σ0 _ λ x → Σ (∃ _ λ n → FirstWitness a x xs n) λ _ → a x
{-# COMPILE AGDA2HS First #-}

pattern FHere {x} h = ⟨ x ⟩ (zero ⟨ isZero refl ⟩ , h)
fHere : a x → First a (x ∷ xs)
fHere x = FHere x
{-# COMPILE AGDA2HS fHere inline #-}

pattern FThere {x} h n h' h'' = ⟨ x ⟩ (suc n ⟨ isSuc h h' ⟩ , h'')
fThere : @0 ¬ a y → First a xs → First a (y ∷ xs)
fThere p = λ where (< n ⟨ q ⟩ , r >) → FThere p n q r
{-# COMPILE AGDA2HS fThere inline #-}

tailFirst : ¬ a x → First a (x ∷ xs) → First a xs
tailFirst ¬r (FHere r) = contradiction r ¬r
tailFirst ¬r (FThere p n q r) = < n ⟨ q ⟩ , r >

¬First[] : ¬ First a []
¬First[] _ = undefined

firstDecP : ∀ {e} {a : @0 e → Type}
  → (∀ x → DecP (a x))
  → ∀ xs → DecP (First a xs)
firstDecP f [] = No ¬First[]
firstDecP f (x ∷ xs) = ifDecP (f x)
  (λ ⦃ p ⦄ → Yes (fHere p))
  (λ ⦃ ¬p ⦄ → mapDecP (fThere ¬p) (tailFirst ¬p) (firstDecP f xs))
{-# COMPILE AGDA2HS firstDecP #-}

module _
  (f : (@0 xs : List e) → Type)
  (h : ∀ {@0 x xs} → a x → f (x ∷ xs))
  (t : ∀ {@0 x xs} → @0 ¬ a x → f xs → f (x ∷ xs))
  where

  wRecFirst : (n : Nat) → @0 FirstWitness a x xs n → a x → f xs
  wRecFirst n p q =
    ifDec (n ≟ 0)
      (λ ⦃ r ⦄ →
        invIsZeroF p r (λ ys → f ys) (h q))
      (λ ⦃ r ⦄ →
        invIsSucF p r (λ ys _ → f ys) λ where n refl h p → t h (wRecFirst n p q))
  {-# COMPILE AGDA2HS wRecFirst #-}

  recFirst : First a xs → f xs
  recFirst (⟨ _ ⟩ (n ⟨ p ⟩ , q)) = wRecFirst n p q
  {-# COMPILE AGDA2HS recFirst inline #-}

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
All¬⇒¬Any [] _ = undefined
All¬⇒¬Any (x ∷ xs) (Here q) = x q
All¬⇒¬Any (x ∷ xs) (There n p q) = All¬⇒¬Any xs (< n ⟨ p ⟩ , q >)

¬Any⇒All¬ : ∀ xs → ¬ Any a xs → All (λ x → ¬ a x) xs
¬Any⇒All¬ []       ¬p = []
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

First⇒Any : First a xs → Any a xs
First⇒Any = recFirst (Any _) here (λ _ → there)

¬First⇒¬Any : ¬ First a xs → ¬ Any a xs
¬First⇒¬Any ¬p h =
  recAny (λ xs → ¬ First _ xs → ⊥)
    (λ p ¬p → ¬p (fHere p))
    (λ ih ¬p → ih (¬p ∘ (fThere (¬p ∘ fHere))))
    h ¬p

gmapAny⁺ : {@0 f : e → e'}
  → (∀ {@0 x} → a x → b (f x))
  → Any a xs → Any b (map f xs)
gmapAny⁺ {f = f} g = recAny (λ xs → Any _ (map f xs)) (here ∘ g) there

++Any⁺ˡ : Any a xs → Any a (xs ++ ys)
++Any⁺ˡ {ys = ys} = recAny (λ xs → Any _ (xs ++ ys)) here there

++Any⁺ʳ : ∀ {xs} {@0 ys} → Any a ys → Any a (xs ++ ys)
++Any⁺ʳ {xs = []}     p = p
++Any⁺ʳ {xs = x ∷ xs} p = there (++Any⁺ʳ p)

@0 gconcatMapAny⁺ : {@0 f : e → List e'}
  → (∀ {@0 x} → a x → Any b (f x))
  → Any a xs → Any b (concatMap f xs)
gconcatMapAny⁺ {f = f} g = recAny (λ xs → Any _ (concatMap f xs)) (++Any⁺ˡ ∘ g) ++Any⁺ʳ

++Any⁻ : ∀ xs {@0 ys} → Any a (xs ++ ys) → Either (Any a xs) (Any a ys)
++Any⁻ [] p = Right p
++Any⁻ (x ∷ xs) (Here q) = Left (here q)
++Any⁻ (x ∷ xs) (There n p q) = bimap there id (++Any⁻ xs (< n ⟨ p ⟩ , q >))

gmapAny⁻ : {@0 f : e → e'}
  → (∀ {x} → b (f x) → a x)
  → ∀ {xs} → Any b (map f xs) → Any a xs
gmapAny⁻ g {x ∷ xs} (Here q) = here (g q)
gmapAny⁻ g {x ∷ xs} (There n p q) = there (gmapAny⁻ g (< n ⟨ p ⟩ , q >))

gconcatMapAny⁻ : {f : e → List e'}
  → (∀ {x} → Any b (f x) → a x)
  → ∀ {xs} → Any b (concatMap f xs) → Any a xs
gconcatMapAny⁻ {f = f} g {x ∷ xs} p with ++Any⁻ (f x) p
... | Left q  = here (g q)
... | Right q = there (gconcatMapAny⁻ g q)

¬Some⇒All¬ : ∀ xs → ¬ Some a xs → All (λ x → ¬ a x) xs
¬Some⇒All¬ [] _ = []
¬Some⇒All¬ (x ∷ xs) ¬pxxs =
  (λ px → ¬pxxs (SHere px (trivialMany xs))) ∷ ¬Some⇒All¬ xs (¬pxxs ∘ SThere)
