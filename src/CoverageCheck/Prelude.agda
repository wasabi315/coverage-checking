module CoverageCheck.Prelude where

--------------------------------------------------------------------------------
-- agda2hs re-exports

open import Haskell.Prelude public
  using (Type; id; _∘_; flip; case_of_; undefined;
         ⊤; tt;
         Bool; True; False; not; _&&_; _||_; if_then_else_;
         Nat; zero; suc; _+_;
         List; []; _∷_; _++_; map; foldr; elem; sum; concat; concatMap; lengthNat;
         String;
         _×_; _,_; fst; snd; uncurry;
         Either; Left; Right; either;
         _≡_; refl)

open import Haskell.Prim public
  using (⊥)

open import Haskell.Prim.Eq public
  using (Eq; _==_)
open import Haskell.Law.Eq public
  using (IsLawfulEq; isEquality; eqReflexivity)

open import Haskell.Prim.Foldable public
  using (iFoldableList; Foldable; any)

open import Haskell.Prim.Num public
  using (iNumNat)

open import Haskell.Prim.Ord public
  using (Ord; OrdFromLessThan)

open import Haskell.Prim.Tuple public
  using (first; second)

open import Haskell.Law.Bool public
  using (prop-x-||-True; not-involution)

open import Haskell.Law.Equality public
  using (cong; cong₂; subst; subst0; sym; trans)

open import Haskell.Law.List public
  using (map-++)

open import Haskell.Extra.Dec public
  using (Reflects; mapReflects; extractTrue; extractFalse;
         Dec; mapDec)

open import Haskell.Extra.Erase public
  using (Erase; Erased; get;
         Σ0; ⟨_⟩_; <_>)

Σ0-syntax = Σ0
{-# COMPILE AGDA2HS Σ0-syntax inline #-}
syntax Σ0-syntax A (λ x → B) = Σ0[ x ∈ A ] B
infix 2 Σ0-syntax

open import Haskell.Extra.Refinement public
  using (∃; _⟨_⟩; value; proof; mapRefine)

∃-syntax = ∃
{-# COMPILE AGDA2HS ∃-syntax inline #-}
syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 2 ∃-syntax

open import Haskell.Extra.Sigma public
  using (Σ-syntax; _,_; fst; snd)

open import Data.Set public
  using (Set; empty; singleton; union; fromList; null; member; difference; toAscList;
         prop-member-insert; prop-member-empty; prop-member-union; prop-member-null;
         prop-member-difference; prop-member-fromList; prop-member-toAscList;
         prop-null→empty)

--------------------------------------------------------------------------------
-- Bottom and negation

infix 3 ¬_

¬_ : Type → Type
¬ A = A → ⊥

explode : {a : Type} → @0 ⊥ → a
explode _ = undefined
{-# COMPILE AGDA2HS explode inline #-}

exFalso : {x : Bool} {a : Type} → @0 x ≡ True → @0 x ≡ False → a
exFalso h h' = explode (Haskell.Prim.exFalso h h')
{-# COMPILE AGDA2HS exFalso inline #-}

contradiction : {a b : Type} → a → @0 ¬ a → b
contradiction a ¬a = explode (¬a a)
{-# COMPILE AGDA2HS contradiction inline #-}

contraposition : {a b : Type} → (a → b) → (¬ b → ¬ a)
contraposition f g = g ∘ f

--------------------------------------------------------------------------------
-- Either

mapEither : {a b c d : Type} → (a → c) → (b → d) → Either a b → Either c d
mapEither f g (Left x)  = Left (f x)
mapEither f g (Right y) = Right (g y)
{-# COMPILE AGDA2HS mapEither #-}

--------------------------------------------------------------------------------
-- Set properties

ifTrueFalse : (b : Bool) → (if b then True else False) ≡ b
ifTrueFalse False = refl
ifTrueFalse True  = refl

module _ {a : Type} ⦃ _ : Ord a ⦄ where

  prop-member-singleton : (x y : a)
    → member x (singleton y) ≡ (x == y)
  prop-member-singleton x y
    rewrite prop-member-insert x y empty
    | prop-member-empty x
    | ifTrueFalse (x == y)
    = refl

  prop-difference-empty : {sa sb : Set a}
    → difference sa sb ≡ empty
    → ∀ {x}
    → member x sa ≡ True
    → member x sb ≡ True
  prop-difference-empty {sa} {sb} h {x} h'
    with eq ← prop-member-difference x sa sb
    rewrite h | h' | prop-member-empty x
    = sym (not-involution False (member x sb) eq)

  prop-null-toAscList : {s : Set a}
    → toAscList s ≡ []
    → null s ≡ True
  prop-null-toAscList {s} h = prop-member-null s λ x →
    trans (sym (prop-member-toAscList x s)) (cong (elem x) h)

  findMin : ⦃ @0 _ : IsLawfulEq a ⦄
    → (s : Set a) ⦃ @0 _ : null s ≡ False ⦄
    → ∃[ x ∈ a ] member x s ≡ True
  findMin s ⦃ h ⦄ = case toAscList s of λ where
    []       ⦃ h' ⦄ → exFalso (prop-null-toAscList h') h
    (x ∷ xs) ⦃ h' ⦄ →
      x ⟨ trans (sym (prop-member-toAscList x s))
          (trans (cong (elem x) h')
          (cong (_|| elem x xs) (eqReflexivity x))) ⟩
  {-# COMPILE AGDA2HS findMin #-}

--------------------------------------------------------------------------------
-- Relations on lists

infixr 5 _◂_

data All {@0 a : Type} (p : @0 a → Type) : (@0 xs : List a) → Type where
  AllNil  : All p []
  AllCons : ∀ {@0 x xs} → p x → All p xs → All p (x ∷ xs)

{-# COMPILE AGDA2HS All deriving Show #-}

pattern ⌈⌉       = AllNil
pattern _◂_ h hs = AllCons h hs

headAll : ∀ {@0 a : Type} {p : @0 a → Type} {@0 x xs} → All p (x ∷ xs) → p x
headAll (h ◂ _) = h
{-# COMPILE AGDA2HS headAll #-}

tailAll : ∀ {@0 a : Type} {p : @0 a → Type} {@0 x xs} → All p (x ∷ xs) → All p xs
tailAll (_ ◂ hs) = hs
{-# COMPILE AGDA2HS tailAll #-}

data Any {@0 a : Type} (p : @0 a → Type) : (@0 xs : List a) → Type where
  AnyHere  : ∀ {@0 x xs} → p x → Any p (x ∷ xs)
  AnyThere : ∀ {@0 x xs} → Any p xs → Any p (x ∷ xs)

{-# COMPILE AGDA2HS Any deriving Show #-}

pattern here  h = AnyHere h
pattern there h = AnyThere h

module @0 _ {a : Type} {p : @0 a → Type} where

  All¬⇒¬Any : ∀ {xs} → All (λ x → ¬ p x) xs → ¬ Any p xs
  All¬⇒¬Any (¬p ◂ _)  (here  p) = ¬p p
  All¬⇒¬Any (_  ◂ ¬p) (there p) = All¬⇒¬Any ¬p p

  ¬Any⇒All¬ : ∀ xs → ¬ Any p xs → All (λ x → ¬ p x) xs
  ¬Any⇒All¬ []       ¬p = ⌈⌉
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ◂ ¬Any⇒All¬ xs (¬p ∘ there)

  ++Any⁺ˡ : ∀ {xs ys} → Any p xs → Any p (xs ++ ys)
  ++Any⁺ˡ (here x)  = here x
  ++Any⁺ˡ (there h) = there (++Any⁺ˡ h)

  ++Any⁺ʳ : ∀ {xs ys} → Any p ys → Any p (xs ++ ys)
  ++Any⁺ʳ {[]}     h = h
  ++Any⁺ʳ {x ∷ xs} h = there (++Any⁺ʳ h)

  ++Any⁻ : ∀ xs {ys} → Any p (xs ++ ys) → Either (Any p xs) (Any p ys)
  ++Any⁻ []       h         = Right h
  ++Any⁻ (x ∷ xs) (here h)  = Left (here h)
  ++Any⁻ (x ∷ xs) (there h) = mapEither there id (++Any⁻ xs h)


module @0 _ {a b : Type} {p : @0 a → Type} {q : @0 b → Type} {@0 f : a → List b} where

  gconcatMapAny⁺ :
      (∀ {x} → p x → Any q (f x))
    → (∀ {xs} → Any p xs → Any q (concatMap f xs))
  gconcatMapAny⁺ g {x ∷ xs} (here h)  = ++Any⁺ˡ (g h)
  gconcatMapAny⁺ g {x ∷ xs} (there h) = ++Any⁺ʳ (gconcatMapAny⁺ g h)

  gconcatMapAny⁻ :
      (∀ {x} → Any q (f x) → p x)
    → (∀ {xs : List _} → Any q (concatMap f xs) → Any p xs)
  gconcatMapAny⁻ g {x ∷ xs} h with ++Any⁻ (f x) h
  ... | Left h'  = here (g h')
  ... | Right h' = there (gconcatMapAny⁻ g h')


data First {@0 a : Type} (p : @0 a → Type) : (@0 xs : List a) → Type where
  FirstHere  : ∀ {@0 x xs} → p x → First p (x ∷ xs)
  FirstThere : ∀ {@0 x xs} → @0 ¬ p x → First p xs → First p (x ∷ xs)

{-# COMPILE AGDA2HS First deriving Show #-}

pattern [_] h    = FirstHere h
pattern _◂_ h hs = FirstThere h hs

firstToAny : ∀ {@0 a : Type} {p : @0 a → Type} {@0 xs} → First p xs → Any p xs
firstToAny [ h ]   = here h
firstToAny (_ ◂ h) = there (firstToAny h)
{-# COMPILE AGDA2HS firstToAny #-}

notFirstToNotAny : ∀ {@0 a : Type} {p : @0 a → Type} {@0 xs} → ¬ First p xs → ¬ Any p xs
notFirstToNotAny h (here h')  = h [ h' ]
notFirstToNotAny h (there h') = notFirstToNotAny (h ∘ (h ∘ [_] ◂_)) h'

@0 Fresh : {a : Type} → List a → Type
Fresh []       = ⊤
Fresh (x ∷ xs) = All (λ y → ¬ x ≡ y) xs × Fresh xs

--------------------------------------------------------------------------------
-- Non-empty lists

infixr 5 consNonEmpty appendNonEmpty

record NonEmpty (a : Type) : Type where
  constructor MkNonEmpty
  field
    head : a
    tail : List a

open NonEmpty public
{-# COMPILE AGDA2HS NonEmpty deriving Show #-}

pattern _◂_ x xs = MkNonEmpty x xs

consNonEmpty : {a : Type} → a → NonEmpty a → NonEmpty a
consNonEmpty x (y ◂ ys) = x ◂ (y ∷ ys)
{-# COMPILE AGDA2HS consNonEmpty #-}
syntax consNonEmpty x xs = x ◂′ xs

mapNonEmpty : {a b : Type} → (a → b) → NonEmpty a → NonEmpty b
mapNonEmpty f (x ◂ xs) = f x ◂ map f xs
{-# COMPILE AGDA2HS mapNonEmpty #-}

appendNonEmpty : {a : Type} → NonEmpty a → NonEmpty a → NonEmpty a
appendNonEmpty (x ◂ xs) (y ◂ ys) = x ◂ (xs ++ y ∷ ys)
{-# COMPILE AGDA2HS appendNonEmpty #-}
syntax appendNonEmpty xs ys = xs ◂◂ⁿᵉ ys

concatNonEmpty : {a : Type} → NonEmpty (NonEmpty a) → NonEmpty a
concatNonEmpty (xs ◂ xss) = go xs xss
  where
    go : {a : Type} → NonEmpty a → List (NonEmpty a) → NonEmpty a
    go xs []         = xs
    go xs (ys ∷ xss) = xs ◂◂ⁿᵉ go ys xss
{-# COMPILE AGDA2HS concatNonEmpty #-}

concatMapNonEmpty : {a b : Type} → (a → NonEmpty b) → NonEmpty a → NonEmpty b
concatMapNonEmpty f xs = concatNonEmpty (mapNonEmpty f xs)
{-# COMPILE AGDA2HS concatMapNonEmpty inline #-}

--------------------------------------------------------------------------------
-- Decidable relations

_≟_ : {a : Type} ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ → (x y : a) → Dec (x ≡ y)
x ≟ y = (x == y) ⟨ isEquality x y ⟩
{-# COMPILE AGDA2HS _≟_ inline #-}

ifDec : {@0 a : Type} {b : Type} → Dec a → (@0 ⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
ifDec (b ⟨ p ⟩) x y = if b then (λ where ⦃ refl ⦄ → x ⦃ p ⦄) else (λ where ⦃ refl ⦄ → y ⦃ p ⦄)
{-# COMPILE AGDA2HS ifDec inline #-}

@0 negReflects : ∀ {ba a} → Reflects a ba → Reflects (¬ a) (not ba)
negReflects {False} ¬a = ¬a
negReflects {True}  a  = λ ¬a → ¬a a

negDec : ∀ {@0 a} → Dec a → Dec (¬ a)
negDec (ba ⟨ a ⟩) = not ba ⟨ negReflects a ⟩
{-# COMPILE AGDA2HS negDec inline #-}

infix 3 tupleDec

@0 tupleReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (a × b) (ba && bb)
tupleReflects {False} {_}     ¬a _  = ¬a ∘ fst
tupleReflects {True}  {False} _  ¬b = ¬b ∘ snd
tupleReflects {True}  {True}  a  b  = a , b

tupleDec : ∀ {@0 a b} → Dec a → Dec b → Dec (a × b)
tupleDec (ba ⟨ a ⟩) (bb ⟨ b ⟩) = (ba && bb) ⟨ tupleReflects a b ⟩
{-# COMPILE AGDA2HS tupleDec inline #-}
syntax tupleDec a b = a ×-dec b

@0 eitherReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (Either a b) (ba || bb)
eitherReflects {True}  {_}     a  _  = Left a
eitherReflects {False} {True}  _  b  = Right b
eitherReflects {False} {False} ¬a ¬b = either ¬a ¬b

eitherDec : ∀ {@0 a b} → Dec a → Dec b → Dec (Either a b)
eitherDec (ba ⟨ a ⟩) (bb ⟨ b ⟩) = (ba || bb) ⟨ eitherReflects a b ⟩
{-# COMPILE AGDA2HS eitherDec inline #-}

--------------------------------------------------------------------------------
-- Decidable relation that does not erase positive information

infix 3 tupleDecP

data DecP (a : Type) : Type where
  Yes : (p : a) → DecP a
  No  : (@0 p : ¬ a) → DecP a
{-# COMPILE AGDA2HS DecP deriving Show #-}

mapDecP : ∀ {a b} → (a → b) → @0 (b → a) → DecP a → DecP b
mapDecP f g (Yes p) = Yes (f p)
mapDecP f g (No p)  = No (contraposition g p)
{-# COMPILE AGDA2HS mapDecP #-}

ifDecP : {a b : Type} → DecP a → (⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
ifDecP (Yes p) t e = t ⦃ p ⦄
ifDecP (No p)  t e = e ⦃ p ⦄
{-# COMPILE AGDA2HS ifDecP #-}

tupleDecP : ∀ {a b} → DecP a → DecP b → DecP (a × b)
syntax tupleDecP a b = a ×-decP b
No p  ×-decP _     = No (contraposition fst p)
Yes _ ×-decP No q  = No (contraposition snd q)
Yes p ×-decP Yes q = Yes (p , q)
{-# COMPILE AGDA2HS tupleDecP #-}

eitherDecP : ∀ {a b} → DecP a → DecP b → DecP (Either a b)
eitherDecP (Yes p) _       = Yes (Left p)
eitherDecP (No p)  (Yes q) = Yes (Right q)
eitherDecP (No p)  (No q)  = No (either p q)
{-# COMPILE AGDA2HS eitherDecP #-}

firstDecP : ∀ {a} {p : @0 a → Type}
  → (∀ x → DecP (p x))
  → (∀ xs → DecP (First p xs))
firstDecP         f []       = No λ ()
firstDecP {p = p} f (x ∷ xs) = ifDecP (f x)
  (λ ⦃ h ⦄ → Yes [ h ])
  (λ ⦃ h ⦄ → mapDecP (h ◂_) (lem h) (firstDecP f xs))
  where
    @0 lem : ¬ p x → First p (x ∷ xs) → First p xs
    lem h [ h' ]   = contradiction h' h
    lem h (x ◂ h') = h'
{-# COMPILE AGDA2HS firstDecP #-}
