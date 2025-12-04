module CoverageCheck.Prelude where

{-# FOREIGN AGDA2HS
import Data.Bifoldable (Bifoldable(..))
import Data.Bifoldable1 (Bifoldable1(..))
import Data.Bifunctor (Bifunctor(..))
#-}

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

open import Haskell.Extra.Dec public using
  (Reflects; mapReflects; extractTrue; extractFalse; Dec; mapDec; ifDec)

open import Haskell.Extra.Erase public using
  (Erase; Erased; get; Σ0; ⟨_⟩_; <_>)

Σ0-syntax = Σ0
syntax Σ0-syntax A (λ x → B) = Σ0[ x ∈ A ] B
infix 2 Σ0-syntax
{-# COMPILE AGDA2HS Σ0-syntax inline #-}

open import Haskell.Extra.Refinement public using
  (∃; _⟨_⟩; value; proof; mapRefine)

∃-syntax = ∃
syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 2 ∃-syntax
{-# COMPILE AGDA2HS ∃-syntax inline #-}

open import Haskell.Extra.Sigma public using (Σ; Σ-syntax; _,_; fst; snd)

--------------------------------------------------------------------------------
-- Things in Haskell base but not provided by agda2hs-base

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

infix 3 ¬_

¬_ : Type → Type
¬ a = a → ⊥

explode : {a : Type} → @0 ⊥ → a
explode _ = undefined
{-# COMPILE AGDA2HS explode inline #-}

contradiction : {a b : Type} → a → @0 ¬ a → b
contradiction a ¬a = explode (¬a a)
{-# COMPILE AGDA2HS contradiction inline #-}

contraposition : {a b : Type} → (a → b) → (¬ b → ¬ a)
contraposition f g = g ∘ f

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

module _ {@0 a : Type} (p : @0 a → Type) where

  data All : (@0 xs : List a) → Type where
    Nil  : All []
    _:>_ : ∀ {@0 x xs} → p x → All xs → All (x ∷ xs)

  data Any : (@0 xs : List a) → Type where
    Here  : ∀ {@0 x xs} → p x → Any (x ∷ xs)
    There : ∀ {@0 x xs} → Any xs → Any (x ∷ xs)

  data First : (@0 xs : List a) → Type where
    FHere  : ∀ {@0 x xs} → p x → First (x ∷ xs)
    FThere : ∀ {@0 x xs} → @0 ¬ p x → First xs → First (x ∷ xs)

{-# COMPILE AGDA2HS All   deriving (Eq, Show) #-}
{-# COMPILE AGDA2HS Any   deriving (Eq, Show) #-}
{-# COMPILE AGDA2HS First deriving (Eq, Show) #-}

pattern []       = Nil
pattern _∷_ p ps = p :> ps
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

  headAll : ∀ {@0 x xs} → All p (x ∷ xs) → p x
  headAll (p ∷ _) = p
  {-# COMPILE AGDA2HS headAll #-}

  tailAll : ∀ {@0 x xs} → All p (x ∷ xs) → All p xs
  tailAll (_ ∷ ps) = ps
  {-# COMPILE AGDA2HS tailAll #-}

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


module _ {@0 a : Type} {p q : @0 a → Type} where

  mapAll : (∀ {x} → p x → q x) → (∀ {xs} → All p xs → All q xs)
  mapAll f [] = []
  mapAll f (p ∷ ps) = f p ∷ mapAll f ps


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

data These (a b : Type) : Type where
  This  : a → These a b
  That  : b → These a b
  Both  : a → b → These a b

{-# COMPILE AGDA2HS These deriving (Eq, Show) #-}

these : {a b c : Type} → (a → c) → (b → c) → (a → b → c) → These a b → c
these f g h (This x)   = f x
these f g h (That x)   = g x
these f g h (Both x y) = h x y
{-# COMPILE AGDA2HS these #-}

eitherToThese : {a b : Type} → Either a b → These a b
eitherToThese = either This That
{-# COMPILE AGDA2HS eitherToThese inline #-}

instance
  iDefaultFunctorThese : ∀ {a} → DefaultFunctor (These a)
  iDefaultFunctorThese .DefaultFunctor.fmap f (This x) = This x
  iDefaultFunctorThese .DefaultFunctor.fmap f (That y) = That (f y)
  iDefaultFunctorThese .DefaultFunctor.fmap f (Both x y) = Both x (f y)

  iFunctorThese : ∀ {a} → Functor (These a)
  iFunctorThese = record {DefaultFunctor iDefaultFunctorThese}
  {-# COMPILE AGDA2HS iFunctorThese #-}

  iBifunctorFromBimapThese : BifunctorFromBimap These
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (This x) = This (f x)
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (That y) = That (g y)
  iBifunctorFromBimapThese .BifunctorFromBimap.bimap f g (Both x y) = Both (f x) (g y)

  iBifunctorThese : Bifunctor These
  iBifunctorThese = record {BifunctorFromBimap iBifunctorFromBimapThese}
  {-# COMPILE AGDA2HS iBifunctorThese #-}

  iBifoldableFromBifoldMapThese : BifoldableFromBifoldMap These
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (This x) = f x
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (That y) = g y
  iBifoldableFromBifoldMapThese .BifoldableFromBifoldMap.bifoldMap f g (Both x y) = f x <> g y

  iBifoldableThese : Bifoldable These
  iBifoldableThese = record {BifoldableFromBifoldMap iBifoldableFromBifoldMapThese}
  {-# COMPILE AGDA2HS iBifoldableThese #-}

  iBifoldable1These : Bifoldable1 These
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (This x) = f x
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (That y) = g y
  iBifoldable1These .Bifoldable1.bifoldMap1 f g (Both x y) = f x <> g y
  {-# COMPILE AGDA2HS iBifoldable1These #-}

--------------------------------------------------------------------------------
-- Non-empty lists

open import Haskell.Data.List.NonEmpty using (NonEmpty; _∷_; _<|_)

mapNonEmptyRefine : {a : Type} {@0 p q : a → Type}
  → (@0 f : ∀ {x} → p x → q x)
  → NonEmpty (∃[ x ∈ a ] p x)
  → NonEmpty (∃[ x ∈ a ] q x)
mapNonEmptyRefine f (x ∷ xs) = mapRefine f x ∷ mapListRefine f xs
{-# COMPILE AGDA2HS mapNonEmptyRefine transparent #-}

partitionEithersNonEmpty : {a b : Type}
  → NonEmpty (Either a b)
  → These (NonEmpty a) (NonEmpty b)
partitionEithersNonEmpty {a} {b} (x ∷ xs) = go x xs
  where
    cons : Either a b → These (NonEmpty a) (NonEmpty b) → These (NonEmpty a) (NonEmpty b)
    cons (Left x)  (This xs)    = This (x <| xs)
    cons (Left x)  (That ys)    = Both (x ∷ []) ys
    cons (Left x)  (Both xs ys) = Both (x <| xs) ys
    cons (Right y) (This xs)    = Both xs (y ∷ [])
    cons (Right y) (That ys)    = That (y <| ys)
    cons (Right y) (Both xs ys) = Both xs (y <| ys)

    go : Either a b → List (Either a b) → These (NonEmpty a) (NonEmpty b)
    go x         (y ∷ xs) = cons x (go y xs)
    go (Left x)  []       = This (x ∷ [])
    go (Right y) []       = That (y ∷ [])

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

negReflects : ∀ {ba a} → Reflects a ba → Reflects (¬ a) (not ba)
negReflects {False} ¬a = ¬a
negReflects {True}  a  = λ ¬a → ¬a a

tupleReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (a × b) (ba && bb)
tupleReflects {False} {_}     ¬a _  = ¬a ∘ fst
tupleReflects {True}  {False} _  ¬b = ¬b ∘ snd
tupleReflects {True}  {True}  a  b  = a , b

eitherReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (Either a b) (ba || bb)
eitherReflects {True}  {_}     a  _  = Left a
eitherReflects {False} {True}  _  b  = Right b
eitherReflects {False} {False} ¬a ¬b = either ¬a ¬b

theseReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (These a b) (ba || bb)
theseReflects {True}  {False} a  _  = This a
theseReflects {False} {True}  _  b  = That b
theseReflects {True}  {True}  a  b  = Both a b
theseReflects {False} {False} ¬a ¬b = these ¬a ¬b (λ _ → ¬b)

negDec : ∀ {@0 a} → Dec a → Dec (¬ a)
negDec (ba ⟨ ra ⟩) = (not ba) ⟨ negReflects ra ⟩
{-# COMPILE AGDA2HS negDec inline #-}

tupleDec : ∀ {@0 a b} → Dec a → Dec b → Dec (a × b)
tupleDec (ba ⟨ ra ⟩) (bb ⟨ rb ⟩) = (ba && bb) ⟨ tupleReflects ra rb ⟩
syntax tupleDec a b = a ×-dec b
{-# COMPILE AGDA2HS tupleDec inline #-}

eitherDec : ∀ {@0 a b} → Dec a → Dec b → Dec (Either a b)
eitherDec (ba ⟨ ra ⟩) (bb ⟨ rb ⟩) = (ba || bb) ⟨ eitherReflects ra rb ⟩
{-# COMPILE AGDA2HS eitherDec inline #-}

theseDec : ∀ {@0 a b} → Dec a → Dec b → Dec (These a b)
theseDec (ba ⟨ ra ⟩) (bb ⟨ rb ⟩) = (ba || bb) ⟨ theseReflects ra rb ⟩
{-# COMPILE AGDA2HS theseDec inline #-}

T : Bool → Type
T True  = ⊤
T False = ⊥

@0 dec-stable : ∀ {@0 a} → Dec a → ¬ ¬ a → a
dec-stable (True  ⟨ a  ⟩) ¬¬a = a
dec-stable (False ⟨ ¬a ⟩) ¬¬a = contradiction ¬a ¬¬a

--------------------------------------------------------------------------------
-- Decidable relation that does not erase positive information

infix 3 tupleDecP

data DecP (a : Type) : Type where
  Yes : (p : a) → DecP a
  No  : (@0 p : ¬ a) → DecP a
{-# COMPILE AGDA2HS DecP deriving Show #-}

mapDecP : ∀ {a b} → (a → b) → @0 (b → a) → DecP a → DecP b
mapDecP f g (Yes p) = Yes (f p)
mapDecP f g (No ¬p) = No (contraposition g ¬p)
{-# COMPILE AGDA2HS mapDecP #-}

ifDecP : {a b : Type} → DecP a → (⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
ifDecP (Yes p) t e = t ⦃ p ⦄
ifDecP (No ¬p) t e = e ⦃ ¬p ⦄
{-# COMPILE AGDA2HS ifDecP #-}

decToDecP : ∀ {@0 a} → Dec a → DecP (Erase a)
decToDecP (False ⟨ ¬a ⟩) = No λ (Erased a) → contradiction a ¬a
decToDecP (True  ⟨ a  ⟩) = Yes (Erased a)
{-# COMPILE AGDA2HS decToDecP #-}

tupleDecP : ∀ {a b} → DecP a → DecP b → DecP (a × b)
syntax tupleDecP a b = a ×-decP b
No ¬p ×-decP _     = No (contraposition fst ¬p)
Yes _ ×-decP No ¬q = No (contraposition snd ¬q)
Yes p ×-decP Yes q = Yes (p , q)
{-# COMPILE AGDA2HS tupleDecP #-}

eitherDecP : ∀ {a b} → DecP a → DecP b → DecP (Either a b)
eitherDecP (Yes p) _       = Yes (Left p)
eitherDecP (No ¬p) (Yes q) = Yes (Right q)
eitherDecP (No ¬p) (No ¬q) = No (either ¬p ¬q)
{-# COMPILE AGDA2HS eitherDecP #-}

theseDecP : ∀ {a b} → DecP a → DecP b → DecP (These a b)
theseDecP (Yes p) (Yes q) = Yes (Both p q)
theseDecP (Yes p) (No ¬q) = Yes (This p)
theseDecP (No ¬p) (Yes q) = Yes (That q)
theseDecP (No ¬p) (No ¬q) = No (these ¬p ¬q (λ _ → ¬q))
{-# COMPILE AGDA2HS theseDecP #-}

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

--------------------------------------------------------------------------------
-- Sets

open import Data.Set as Set using (Set)

||-leftFalse : (x y : Bool) → (x || y) ≡ False → x ≡ False
||-leftFalse False y _ = refl

module _ {a : Type} ⦃ _ : Ord a ⦄ where
  open import Agda.Builtin.Equality.Erase

  -- Wrap the postulated properties of Set with primEraseEquality.
  -- These wrapped properties reduce to refl when the sides are definitionally equal.
  -- This wrapping does not affect the validity of the proofs; we are merely
  -- encapsulating the reliable properties from agda2hs.

  prop-null→empty : (s : Set a) → Set.null s ≡ True → s ≡ Set.empty
  prop-null→empty s eq = primEraseEquality (Set.prop-null→empty s eq)

  prop-member-fromList : (x : a) (xs : List a)
    → Set.member x (Set.fromList xs) ≡ elem x xs
  prop-member-fromList x xs = primEraseEquality (Set.prop-member-fromList x xs)

  prop-member-toAscList : (x : a) (s : Set a)
    → elem x (Set.toAscList s) ≡ Set.member x s
  prop-member-toAscList x s = primEraseEquality (Set.prop-member-toAscList x s)

  prop-member-empty : (x : a) → Set.member x Set.empty ≡ False
  prop-member-empty x = primEraseEquality (Set.prop-member-empty x)

  prop-member-insert : ∀ (x y : a) (s : Set a)
    → Set.member x (Set.insert y s) ≡ (x == y || Set.member x s)
  prop-member-insert x y s
    rewrite primEraseEquality (Set.prop-member-insert x y s)
    with x == y
  ... | True  = refl
  ... | False = refl

  prop-member-union : ∀ (x : a) (s1 s2 : Set a)
    → Set.member x (Set.union s1 s2) ≡ (Set.member x s1 || Set.member x s2)
  prop-member-union x s1 s2 = primEraseEquality (Set.prop-member-union x s1 s2)

  prop-member-difference : ∀ (x : a) (s1 s2 : Set a)
    → Set.member x (Set.difference s1 s2) ≡ (Set.member x s1 && not (Set.member x s2))
  prop-member-difference x s1 s2 = primEraseEquality (Set.prop-member-difference x s1 s2)

  prop-member-null : (s : Set a)
    → (∀ x → Set.member x s ≡ False) → Set.null s ≡ True
  prop-member-null s eq = primEraseEquality (Set.prop-member-null s eq)

  prop-member-singleton : (x y : a)
    → Set.member x (Set.singleton y) ≡ (x == y)
  prop-member-singleton x y
    rewrite prop-member-insert x y Set.empty
    | prop-member-empty x
    = prop-x-||-False _

  prop-equality : {s1 s2 : Set a}
    → (∀ x → Set.member x s1 ≡ Set.member x s2)
    → s1 ≡ s2
  prop-equality h = primEraseEquality (Set.prop-equality h)

  prop-union-identity : {s : Set a}
    → Set.union s Set.empty ≡ s
  prop-union-identity = primEraseEquality Set.prop-union-identity

  prop-union-sym : {sa sb : Set a}
    → Set.union sa sb ≡ Set.union sb sa
  prop-union-sym = primEraseEquality Set.prop-union-sym

  prop-null-empty : Set.null {a} Set.empty ≡ True
  prop-null-empty = primEraseEquality Set.prop-null-empty

  prop-null-insert : ⦃ _ : IsLawfulEq a ⦄
    → (x : a) (s : Set a)
    → Set.null (Set.insert x s) ≡ False
  prop-null-insert x s with Set.null (Set.insert x s) in eq
  ... | False = refl
  ... | True  =
          trans (sym (cong (_|| Set.member x s) (eqReflexivity x)))
          (trans (sym (prop-member-insert x x s))
          (trans (cong (Set.member x) (prop-null→empty _ eq))
          (Set.prop-member-empty x)))

  prop-null-toAscList : {s : Set a}
    → Set.toAscList s ≡ []
    → Set.null s ≡ True
  prop-null-toAscList {s} eq = prop-member-null s λ x →
    trans (sym (prop-member-toAscList x s)) (cong (elem x) eq)

  prop-null-union-left : {s1 s2 : Set a}
    → Set.null (Set.union s1 s2) ≡ True
    → Set.null s1 ≡ True
  prop-null-union-left eq = prop-member-null _ λ x →
    ||-leftFalse (Set.member x _) (Set.member x _)
      (trans (sym (prop-member-union x _ _))
      (trans (cong (Set.member x) (prop-null→empty _ eq))
      (prop-member-empty x)))

  prop-null-union-right : {s1 s2 : Set a}
    → Set.null (Set.union s1 s2) ≡ True
    → Set.null s2 ≡ True
  prop-null-union-right {s1 = s1} {s2} eq
    rewrite prop-union-sym {sa = s1} {sb = s2}
    = prop-null-union-left eq

  prop-null-union' : {s1 s2 : Set a}
    → Set.null s1 ≡ True
    → Set.null s2 ≡ True
    → Set.null (Set.union s1 s2) ≡ True
  prop-null-union' {s1 = s1} {s2} eq1 eq2
    rewrite prop-null→empty s2 eq2
    | prop-union-identity {s = s1}
    = eq1

  prop-null-union : (s1 s2 : Set a)
    → Set.null (Set.union s1 s2) ≡ (Set.null s1 && Set.null s2)
  prop-null-union s1 s2
    with Set.null (Set.union s1 s2) in eq1 | Set.null s1 in eq2 | Set.null s2 in eq3
  ... | False | False | _     = refl
  ... | False | True  | False = refl
  ... | True  | True  | True  = refl
  ... | True  | False | _     = explode (exFalso (prop-null-union-left eq1) eq2)
  ... | True  | True  | False = explode (exFalso (prop-null-union-right eq1) eq3)
  ... | False | True  | True  = explode (exFalso (prop-null-union' eq2 eq3) eq1)

  prop-difference-empty : {sa sb : Set a}
    → Set.difference sa sb ≡ Set.empty
    → ∀ {x}
    → Set.member x sa ≡ True
    → Set.member x sb ≡ True
  prop-difference-empty {sa} {sb} eq1 {x} eq2
    with eq3 ← prop-member-difference x sa sb
    rewrite eq1 | eq2 | prop-member-empty x
    = sym (not-involution False (Set.member x sb) eq3)

  toAscListW' : ⦃ @0 _ : IsLawfulEq a ⦄
    → {@0 s : Set a} (xs : List a)
    → (@0 f : ∀ {x} → elem x xs ≡ True → Set.member x s ≡ True)
    → List (∃[ x ∈ a ] Set.member x s ≡ True)
  toAscListW' []       f = []
  toAscListW' (x ∷ xs) f =
    x ⟨ f (cong (_|| elem x xs) (eqReflexivity x)) ⟩ ∷
    toAscListW' xs λ h → f (trans (cong (_ ||_) h) (prop-x-||-True _))
  {-# COMPILE AGDA2HS toAscListW' transparent #-}

  toAscNonEmptyW : ⦃ @0 _ : IsLawfulEq a ⦄
    → (s : Set a)
    → Either
        (Erase (∀ x → Set.member x s ≡ False))
        (NonEmpty (∃[ x ∈ a ] Set.member x s ≡ True))
  toAscNonEmptyW s = case Set.toAscList s of λ where
    [] ⦃ eq ⦄ →
      Left (Erased λ x → trans (sym (prop-member-toAscList x s)) (cong (elem x) eq))
    (x ∷ xs) ⦃ eq ⦄ →
      let @0 f : ∀ {y} → elem y (x ∷ xs) ≡ True → Set.member y s ≡ True
          f eq2 = trans (sym (prop-member-toAscList _ s)) (trans (cong (elem _) eq) eq2)
       in Right (x ⟨ f (cong (_|| elem x xs) (eqReflexivity x)) ⟩ ∷
                 toAscListW' xs λ eq3 → f (trans (cong (_ ||_) eq3) (prop-x-||-True _)))
  {-# COMPILE AGDA2HS toAscNonEmptyW inline #-}
