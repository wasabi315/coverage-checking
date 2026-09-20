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

open import CoverageCheck.Data.List.All as All public
open import CoverageCheck.Data.List.Any as Any public
open import CoverageCheck.Data.List.First as First public
open import CoverageCheck.Data.List.Many as Many public
open import CoverageCheck.Data.List.Some as Some public
open import CoverageCheck.Data.List.HPointwise as HPointwise public

pattern [] = All.Nil
pattern _∷_ p ps = p All.:> ps
pattern here p = Any.Here p
pattern there p = Any.There p
pattern [_] p = FHere p
pattern _∷_ p ps = FThere p ps
pattern [] = MNil
pattern _∷_ p ps = MHere p ps
pattern there ps = MThere ps
pattern _∷_ p ps = SHere p ps
pattern there ps = SThere ps
pattern [] = HNil
pattern _∷_ rx rxs = rx :>> rxs

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
