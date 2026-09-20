module CoverageCheck.Prelude where

infixr 5 _∷_

--------------------------------------------------------------------------------
-- agda2hs re-exports

open import Haskell.Prelude public using
  ( Type; id; _∘_; _$_; flip; case_of_; undefined;
    ⊤; tt;
    Bool; True; False; not; _&&_; _||_; if_then_else_;
    Nat; zero; suc; _+_;
    List; _++_; map; foldr; foldMap; elem; sum; concat; concatMap; lengthNat; null; iMonadList; reverse; foldl;
    String;
    _×_; _,_; fst; snd; uncurry;
    Maybe; Just; Nothing; maybe;
    Either; Left; Right; either;
    Semigroup; _<>_;
    Functor; DefaultFunctor; fmap;
    Applicative; DefaultApplicative; pure; _<*>_; _<*_; _*>_;
    Monad; DefaultMonad; _>>=_;
    _≡_; refl )

-- For overloading
pattern []       = List.[]
pattern _∷_ x xs = List._∷_ x xs

open import Haskell.Prim public using (⊥; the; Level; exFalso)

open import Haskell.Prim.Eq public using (Eq; _==_; _/=_; iEqList; iEqChar)
open import Haskell.Law.Eq public using
  (IsLawfulEq; isEquality; eqReflexivity; _≟_; iLawfulEqList; iLawfulEqChar)

open import Haskell.Prim.Foldable public using (iFoldableList; Foldable; any)

open import Haskell.Prim.List public using (scanl)

open import Haskell.Prim.Num public using (iNumNat)

open import Haskell.Prim.Ord public using (Ord; OrdFromLessThan; _<_; iOrdList; iOrdChar)

open import Haskell.Law.Bool public using
  (prop-x-||-True; prop-x-||-False; not-involution; not-not)

open import Haskell.Law.Equality public using
  (cong; cong₂; subst; subst0; sym; trans)

open import Haskell.Law.List public using (map-++)

open import Haskell.Extra.Erase public using
  (Erase; Erased; get; Σ0; ⟨_⟩_; <_>)

Σ0-syntax : (@0 a : Type) (b : @0 a → Type) → Type
Σ0-syntax a b = Σ0 a λ x → b x
syntax Σ0-syntax A (λ x → B) = Σ0[ x ∈ A ] B
infix 2 Σ0-syntax
{-# COMPILE AGDA2HS Σ0-syntax inline #-}

open import Haskell.Extra.Refinement public using
  (∃; _⟨_⟩; value; proof; mapRefine)

∃-syntax : (a : Type) (@0 P : a → Type) → Type
∃-syntax a P = ∃ a λ x → P x
syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 2 ∃-syntax
{-# COMPILE AGDA2HS ∃-syntax inline #-}

open import Haskell.Extra.Sigma public using (Σ; Σ-syntax; _,_; fst; snd)

--------------------------------------------------------------------------------
-- Things in Haskell base but not provided by agda2hs-base

open import Haskell.Data.Foldable1 public using
  ( Foldable1; foldMap1 )

open import Haskell.Data.Bifunctor public using
  ( Bifunctor; bimap; first; second;
    BifunctorFromBimap; BifunctorFromFirstSecond;
    iBifunctorTuple; iBifunctorEither )

open import Haskell.Data.Bifoldable public using
  ( Bifoldable; bifoldMap; bifoldr; bifold;
    BifoldableFromBifoldMap; BifoldableFromBifoldr;
    iBifoldableTuple; iBifoldableEither )

open import Haskell.Data.Bifoldable1 public using
  (Bifoldable1; bifoldMap1; bifold1; iBifoldable1Tuple; iBifoldable1Either)

--------------------------------------------------------------------------------
-- Bottom and negation

open import CoverageCheck.Extra.Negation public

--------------------------------------------------------------------------------
-- Equality

cong0 : {@0 a : Type} {b : Type} {@0 x y : a} (f : @0 a → b)
  → @0 x ≡ y
  → f x ≡ f y
cong0 f eq = subst0 (λ z → f _ ≡ f z) eq refl

--------------------------------------------------------------------------------
-- Utility

mapListRefine : {a : Type} {@0 p q : a → Type}
  → (@0 f : ∀ {x} → p x → q x)
  → List (∃[ x ∈ a ] p x)
  → List (∃[ x ∈ a ] q x)
mapListRefine f []       = []
mapListRefine f (x ∷ xs) = mapRefine f x ∷ mapListRefine f xs
{-# COMPILE AGDA2HS mapListRefine transparent #-}

--------------------------------------------------------------------------------
-- Relations on lists

open import CoverageCheck.Data.List.All.Core as All public

pattern [] = All.Nil
pattern _∷_ p ps = p All.:> ps

module _ {@0 a : Type} (p : @0 a → Type) where

  data Any : (@0 xs : List a) → Type where
    Here  : ∀ {@0 x xs} → p x → Any (x ∷ xs)
    There : ∀ {@0 x xs} → Any xs → Any (x ∷ xs)

  data First : (@0 xs : List a) → Type where
    FHere  : ∀ {@0 x xs} → p x → First (x ∷ xs)
    FThere : ∀ {@0 x xs} → @0 ¬ p x → First xs → First (x ∷ xs)

{-# COMPILE AGDA2HS Any   deriving (Eq, Show) #-}
{-# COMPILE AGDA2HS First deriving (Eq, Show) #-}

pattern here  p  = Here p
pattern there p  = There p
pattern [_] p    = FHere p
pattern _∷_ p ps = FThere p ps

module _ {@0 a : Type} (p : @0 a → Type) where

  data Many : (@0 xs : List a) → Type where
    MNil   : Many []
    MHere  : ∀ {@0 x xs} → p x → Many xs → Many (x ∷ xs)
    MThere : ∀ {@0 x xs} → Many xs → Many (x ∷ xs)

  data Some : (@0 xs : List a) → Type where
    SHere  : ∀ {@0 x xs} → p x → Many xs → Some (x ∷ xs)
    SThere : ∀ {@0 x xs} → Some xs → Some (x ∷ xs)

  {-# COMPILE AGDA2HS Many deriving (Eq, Show) #-}
  {-# COMPILE AGDA2HS Some deriving (Eq, Show) #-}

pattern []       = MNil
pattern _∷_ p ps = MHere p ps
pattern _∷_ p ps = SHere p ps
pattern there ps = MThere ps
pattern there ps = SThere ps

data HPointwise
  {@0 a : Type} {@0 p q : @0 a → Type}
  (r : ∀ {@0 x} → @0 p x → @0 q x → Type)
  : ∀ {@0 xs} → @0 All p xs → @0 All q xs → Type
  where
  HNil  : HPointwise r [] []
  _:>>_ : ∀ {@0 x xs}
    → {@0 px : p x} {@0 pxs : All p xs}
    → {@0 qx : q x} {@0 qxs : All q xs}
    → r px qx
    → HPointwise r pxs qxs
    → HPointwise r (px ∷ pxs) (qx ∷ qxs)

{-# COMPILE AGDA2HS HPointwise deriving (Eq, Show) #-}

pattern [] = HNil
pattern _∷_ rx rxs = rx :>> rxs

module _ {@0 a : Type} {p : @0 a → Type} where

  All¬⇒¬Any : ∀ {@0 xs} → All (λ x → ¬ p x) xs → ¬ Any p xs
  All¬⇒¬Any (¬p ∷ _)   (here  p) = ¬p p
  All¬⇒¬Any (_  ∷ ¬ps) (there p) = All¬⇒¬Any ¬ps p

  ¬Any⇒All¬ : ∀ xs → ¬ Any p xs → All (λ x → ¬ p x) xs
  ¬Any⇒All¬ []       ¬p = []
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

  ++Any⁺ˡ : ∀ {@0 xs ys} → Any p xs → Any p (xs ++ ys)
  ++Any⁺ˡ (here p)  = here p
  ++Any⁺ˡ (there p) = there (++Any⁺ˡ p)

  ++Any⁺ʳ : ∀ {xs} {@0 ys} → Any p ys → Any p (xs ++ ys)
  ++Any⁺ʳ {[]}     p = p
  ++Any⁺ʳ {x ∷ xs} p = there (++Any⁺ʳ p)

  ++Any⁻ : ∀ xs {@0 ys} → Any p (xs ++ ys) → Either (Any p xs) (Any p ys)
  ++Any⁻ []       p         = Right p
  ++Any⁻ (x ∷ xs) (here p)  = Left (here p)
  ++Any⁻ (x ∷ xs) (there p) = bimap there id (++Any⁻ xs p)

  First⇒Any : ∀ {@0 xs} → First p xs → Any p xs
  First⇒Any [ p ]   = here p
  First⇒Any (_ ∷ ps) = there (First⇒Any ps)

  ¬First⇒¬Any : ∀ {@0 xs} → ¬ First p xs → ¬ Any p xs
  ¬First⇒¬Any ¬p (here p)  = ¬p [ p ]
  ¬First⇒¬Any ¬p (there p) = ¬First⇒¬Any (¬p ∘ (¬p ∘ [_] ∷_)) p

  tailFirst : ∀ {@0 x xs} → ¬ p x → First p (x ∷ xs) → First p xs
  tailFirst ¬p [ p ]   = contradiction p ¬p
  tailFirst ¬p (_ ∷ p) = p

  tailMany : ∀ {@0 x xs} → Many p (x ∷ xs) → Many p xs
  tailMany (_ ∷ ps)   = ps
  tailMany (there ps) = ps
  {-# COMPILE AGDA2HS tailMany #-}

  someToAny : ∀ {@0 xs} → Some p xs → Many p xs
  someToAny (px ∷ pxs) = px ∷ pxs
  someToAny (there pxs) = there (someToAny pxs)
  {-# COMPILE AGDA2HS someToAny #-}

  tailSome : ∀ {@0 x xs} → Some p (x ∷ xs) → Many p xs
  tailSome (px ∷ pxs) = pxs
  tailSome (there pxs) = someToAny pxs
  {-# COMPILE AGDA2HS tailSome #-}

  unthereSome : ∀ {@0 x xs} → @0 ¬ p x → Some p (x ∷ xs) → Some p xs
  unthereSome ¬px (px ∷ pxs) = contradiction px ¬px
  unthereSome ¬px (there pxs) = pxs
  {-# COMPILE AGDA2HS unthereSome #-}

  trivialMany : ∀ xs → Many p xs
  trivialMany [] = []
  trivialMany (_ ∷ xs) = there (trivialMany xs)

  ¬Some⇒All¬ : ∀ xs → ¬ Some p xs → All (λ x → ¬ p x) xs
  ¬Some⇒All¬ [] _ = []
  ¬Some⇒All¬ (x ∷ xs) ¬pxxs =
    (λ px → ¬pxxs (px ∷ trivialMany xs)) ∷ ¬Some⇒All¬ xs (¬pxxs ∘ there)


module _ {@0 a b : Type} {p : @0 a → Type} {q : @0 b → Type} {f : a → b} where

  gmapAny⁺
    : (∀ {x} → p x → q (f x))
    → (∀ {xs} → Any p xs → Any q (map f xs))
  gmapAny⁺ g {x ∷ xs} (here p)  = here (g p)
  gmapAny⁺ g {x ∷ xs} (there p) = there (gmapAny⁺ g p)

  gmapAny⁻
    : (∀ {x} → q (f x) → p x)
    → (∀ {xs} → Any q (map f xs) → Any p xs)
  gmapAny⁻ g {x ∷ xs} (here p)  = here (g p)
  gmapAny⁻ g {x ∷ xs} (there p) = there (gmapAny⁻ g p)


module _ {@0 a b : Type} {p : @0 a → Type} {q : @0 b → Type} {f : a → List b} where

  gconcatMapAny⁺
    : (∀ {x} → p x → Any q (f x))
    → (∀ {xs} → Any p xs → Any q (concatMap f xs))
  gconcatMapAny⁺ g {x ∷ xs} (here p)  = ++Any⁺ˡ (g p)
  gconcatMapAny⁺ g {x ∷ xs} (there p) = ++Any⁺ʳ (gconcatMapAny⁺ g p)

  gconcatMapAny⁻
    : (∀ {x} → Any q (f x) → p x)
    → (∀ {xs : List _} → Any q (concatMap f xs) → Any p xs)
  gconcatMapAny⁻ g {x ∷ xs} p with ++Any⁻ (f x) p
  ... | Left q  = here (g q)
  ... | Right q = there (gconcatMapAny⁻ g q)

--------------------------------------------------------------------------------
-- These

open import CoverageCheck.Data.These public

--------------------------------------------------------------------------------
-- Non-empty lists

open import Haskell.Data.List.NonEmpty as NE using (NonEmpty; _<|_)

pattern _∷_ x xs = x NE.:| xs

mapNonEmptyRefine : {a : Type} {@0 p q : a → Type}
  → (@0 f : ∀ {x} → p x → q x)
  → NonEmpty (∃[ x ∈ a ] p x)
  → NonEmpty (∃[ x ∈ a ] q x)
mapNonEmptyRefine f (x ∷ xs) = mapRefine f x ∷ mapListRefine f xs
{-# COMPILE AGDA2HS mapNonEmptyRefine transparent #-}

-- These functions should go in Haskell.Data.List, but it is not possible because
-- agda2hs-base already has the module of the same name.
-- Instead, we use the rewrite rule functionality of agda2hs

inits : {a : Type} → List a → List (List a)
inits = map reverse ∘ scanl (flip _∷_) []

inits1 : {a : Type} → List a → List (NonEmpty a)
inits1 [] = []
inits1 (x ∷ xs) = map (x ∷_) (inits xs)

--------------------------------------------------------------------------------
-- Reflects and Dec

open import CoverageCheck.Extra.Dec public

--------------------------------------------------------------------------------
-- Decidable relation that does not erase positive information

open import CoverageCheck.Extra.DecP public

firstDecP : ∀ {a} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → (∀ xs → DecP (First p xs))
firstDecP f []       = No λ _ → undefined
firstDecP f (x ∷ xs) = ifDecP (f x)
  (λ ⦃ p ⦄ → Yes [ p ])
  (λ ⦃ ¬p ⦄ → mapDecP (¬p ∷_) (tailFirst ¬p) (firstDecP f xs))
{-# COMPILE AGDA2HS firstDecP #-}

manyDecP : {a : Type} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → ∀ xs → DecP (Many p xs)
manyDecP f [] = Yes []
manyDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (px ∷_) tailMany (manyDecP f xs))
    (mapDecP there tailMany (manyDecP f xs))
{-# COMPILE AGDA2HS manyDecP #-}

someDecP : {a : Type} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → ∀ xs → DecP (Some p xs)
someDecP f [] = No λ _ → undefined
someDecP f (x ∷ xs) =
  ifDecP (f x)
    (λ ⦃ px ⦄ → mapDecP (px ∷_) tailSome (manyDecP f xs))
    (λ ⦃ ¬px ⦄ → mapDecP there (unthereSome ¬px) (someDecP f xs))
{-# COMPILE AGDA2HS someDecP #-}
