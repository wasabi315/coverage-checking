module CoverageCheck.Prelude where

--------------------------------------------------------------------------------
-- agda2hs re-exports

open import Haskell.Prim public
  using (⊥; the)
open import Haskell.Prim.Tuple public
  using (first; second)

open import Haskell.Prelude public
  using (id; _∘_; flip; case_of_;
         ⊤; tt;
         Bool; True; False; not; _&&_; _||_; if_then_else_;
         Nat; zero; suc;
         List; []; _∷_;
         String;
         _×_; _,_; fst; snd; uncurry;
         Either; Left; Right; either;
         _≡_; refl;
         undefined)
  renaming (Type to Set)

open import Haskell.Prim.Eq public
  using (Eq; _==_)
open import Haskell.Law.Eq public
  using (IsLawfulEq; isEquality)

open import Haskell.Prim.Foldable public
  using (iFoldableList; Foldable; any)

open import Haskell.Law.Equality public
  using (cong; cong₂; subst0; sym)

open import Haskell.Extra.Dec public
  using (Reflects; mapReflects;
         Dec; mapDec)

open import Haskell.Extra.Erase public
  using (Erase; Erased; get;
         Σ0; ⟨_⟩_; <_>)

Σ0-syntax = Σ0
{-# COMPILE AGDA2HS Σ0-syntax inline #-}
syntax Σ0-syntax A (λ x → B) = Σ0[ x ∈ A ] B
infix 2 Σ0-syntax

open import Haskell.Extra.Refinement public
  using (∃; _⟨_⟩; value; proof)

∃-syntax = ∃
{-# COMPILE AGDA2HS ∃-syntax inline #-}
syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 2 ∃-syntax

open import Haskell.Extra.Sigma public
  using (Σ-syntax; _,_; fst; snd)

--------------------------------------------------------------------------------
-- agda standard library re-exports

open import Data.List.Base public
  using (sum; map; _++_; concat; concatMap; length)

--------------------------------------------------------------------------------
-- Utils

_,,_ : {a b : Set} → a → b → a × b
_,,_ = _,_
{-# COMPILE AGDA2HS _,,_ inline #-}

mapEither : {a b c d : Set} → (a → c) → (b → d) → Either a b → Either c d
mapEither f g (Left x)  = Left (f x)
mapEither f g (Right y) = Right (g y)
{-# COMPILE AGDA2HS mapEither #-}

--------------------------------------------------------------------------------
-- Bottom and negation

infix 3 ¬_

¬_ : Set → Set
¬ A = A → ⊥

exFalso : {a : Set} → @0 ⊥ → a
exFalso _ = undefined

contradiction : {a b : Set} → a → @0 ¬ a → b
contradiction a ¬a = exFalso (¬a a)

contraposition : {a b : Set} → (a → b) → (¬ b → ¬ a)
contraposition f g = g ∘ f

--------------------------------------------------------------------------------
-- Relations on lists

infixr 5 _◂_

data All {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  AllNil  : All p []
  AllCons : ∀ {@0 x xs} → p x → All p xs → All p (x ∷ xs)

{-# COMPILE AGDA2HS All deriving Show #-}

pattern ⌈⌉       = AllNil
pattern _◂_ h hs = AllCons h hs

headAll : ∀ {@0 a : Set} {p : @0 a → Set} {@0 x xs} → All p (x ∷ xs) → p x
headAll (h ◂ _) = h
{-# COMPILE AGDA2HS headAll #-}

tailAll : ∀ {@0 a : Set} {p : @0 a → Set} {@0 x xs} → All p (x ∷ xs) → All p xs
tailAll (_ ◂ hs) = hs
{-# COMPILE AGDA2HS tailAll #-}

data Any {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  AnyHere  : ∀ {@0 x xs} → p x → Any p (x ∷ xs)
  AnyThere : ∀ {@0 x xs} → Any p xs → Any p (x ∷ xs)

{-# COMPILE AGDA2HS Any deriving Show #-}

pattern here  h = AnyHere h
pattern there h = AnyThere h

module @0 _ {a : Set} {p : @0 a → Set} where

  ++Any⁺ˡ : ∀ {xs ys} → Any p xs → Any p (xs ++ ys)
  ++Any⁺ˡ (here x)  = here x
  ++Any⁺ˡ (there h) = there (++Any⁺ˡ h)

  ++Any⁺ʳ : ∀ {xs ys} → Any p ys → Any p (xs ++ ys)
  ++Any⁺ʳ {[]}     h = h
  ++Any⁺ʳ {x ∷ xs} h = there (++Any⁺ʳ h)

  ++Any⁻ : ∀ xs {ys} → Any p (xs ++ ys) → Either (Any p xs) (Any p ys)
  ++Any⁻ []       h = Right h
  ++Any⁻ (x ∷ xs) (here h) = Left (here h)
  ++Any⁻ (x ∷ xs) (there h) with ++Any⁻ xs h
  ... | Left h'  = Left (there h')
  ... | Right h' = Right h'

  concatAny⁺ : ∀ {xss} → Any (Any p) xss → Any p (concat xss)
  concatAny⁺ (here h) = ++Any⁺ˡ h
  concatAny⁺ (there h) = ++Any⁺ʳ (concatAny⁺ h)

  concatAny⁻ : ∀ xss → Any p (concat xss) → Any (Any p) xss
  concatAny⁻ ([] ∷ xss)       h         = there (concatAny⁻ xss h)
  concatAny⁻ ((x ∷ xs) ∷ xss) (here h)  = here (here h)
  concatAny⁻ ((x ∷ xs) ∷ xss) (there h) with concatAny⁻ (xs ∷ xss) h
  ... | here h'  = here (there h')
  ... | there h' = there h'

  gmapAny⁺ : {b : Set} {q : @0 b → Set} {f : a → b}
    → (∀ {x} → p x → q (f x))
    → (∀ {xs} → Any p xs → Any q (map f xs))
  gmapAny⁺ g (here h)  = here (g h)
  gmapAny⁺ g (there h) = there (gmapAny⁺ g h)

  gmapAny⁻ : {b : Set} {q : @0 b → Set} {f : a → b}
    → (∀ {x} → q (f x) → p x)
    → (∀ {xs} → Any q (map f xs) → Any p xs)
  gmapAny⁻ g {x ∷ xs} (here h)  = here (g h)
  gmapAny⁻ g {x ∷ xs} (there h) = there (gmapAny⁻ g h)

  ¬Any⇒All¬ : ∀ xs → ¬ Any p xs → All (λ x → ¬ p x) xs
  ¬Any⇒All¬ []       ¬p = ⌈⌉
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ◂ ¬Any⇒All¬ xs (¬p ∘ there)

data First {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  FirstHere  : ∀ {@0 x xs} → p x → First p (x ∷ xs)
  FirstThere : ∀ {@0 x xs} → @0 ¬ p x → First p xs → First p (x ∷ xs)

{-# COMPILE AGDA2HS First deriving Show #-}

pattern [_] h    = FirstHere h
pattern _◂_ h hs = FirstThere h hs

firstToAny : ∀ {@0 a : Set} {p : @0 a → Set} {@0 xs} → First p xs → Any p xs
firstToAny [ h ]   = here h
firstToAny (_ ◂ h) = there (firstToAny h)
{-# COMPILE AGDA2HS firstToAny #-}

notFirstToNotAny : ∀ {@0 a : Set} {p : @0 a → Set} {@0 xs} → ¬ First p xs → ¬ Any p xs
notFirstToNotAny h (here h')  = h [ h' ]
notFirstToNotAny h (there h') = notFirstToNotAny (h ∘ (h ∘ [_] ◂_)) h'

@0 Fresh : {a : Set} → List a → Set
Fresh []       = ⊤
Fresh (x ∷ xs) = All (λ y → ¬ x ≡ y) xs × Fresh xs

--------------------------------------------------------------------------------
-- Non-empty lists

infixr 5 consNonEmpty appendNonEmpty

record NonEmpty (a : Set) : Set where
  constructor MkNonEmpty
  field
    head : a
    tail : List a

open NonEmpty public
{-# COMPILE AGDA2HS NonEmpty deriving Show #-}

pattern _◂_ x xs = MkNonEmpty x xs

consNonEmpty : {a : Set} → a → NonEmpty a → NonEmpty a
consNonEmpty x (y ◂ ys) = x ◂ (y ∷ ys)
{-# COMPILE AGDA2HS consNonEmpty #-}
syntax consNonEmpty x xs = x ◂′ xs

mapNonEmpty : {a b : Set} → (a → b) → NonEmpty a → NonEmpty b
mapNonEmpty f (x ◂ xs) = f x ◂ map f xs
{-# COMPILE AGDA2HS mapNonEmpty #-}

appendNonEmpty : {a : Set} → NonEmpty a → NonEmpty a → NonEmpty a
appendNonEmpty (x ◂ xs) (y ◂ ys) = x ◂ (xs ++ y ∷ ys)
{-# COMPILE AGDA2HS appendNonEmpty #-}
syntax appendNonEmpty xs ys = xs ◂◂ⁿᵉ ys

--------------------------------------------------------------------------------
-- These

data These (a b : Set) : Set where
  This : a → These a b
  That : b → These a b
  Both : a → b → These a b

{-# COMPILE AGDA2HS These deriving Show #-}

these : {a b c : Set} → (a → c) → (b → c) → (a → b → c) → These a b → c
these f g h (This x)   = f x
these f g h (That y)   = g y
these f g h (Both x y) = h x y
{-# COMPILE AGDA2HS these #-}

mapThese : {a b c d : Set} → (a → c) → (b → d) → These a b → These c d
mapThese f g (This x) = This (f x)
mapThese f g (That x) = That (g x)
mapThese f g (Both x y) = Both (f x) (g y)
{-# COMPILE AGDA2HS mapThese #-}

partitionEither : {a b : Set} → NonEmpty (Either a b) → These (NonEmpty a) (NonEmpty b)
partitionEither (x ◂ xs) = go x xs
  where
    go : {a b : Set} → Either a b → List (Either a b) → These (NonEmpty a) (NonEmpty b)
    go x         (y ∷ xs) = case (x ,, go y xs) of λ where
      (Left x  , This xs)    → This (x ◂′ xs)
      (Left x  , That ys)    → Both (x ◂ []) ys
      (Left x  , Both xs ys) → Both (x ◂′ xs) ys
      (Right y , This xs)    → Both xs (y ◂ [])
      (Right y , That ys)    → That (y ◂′ ys)
      (Right y , Both xs ys) → Both xs (y ◂′ ys)
    go (Left x)  []       = This (x ◂ [])
    go (Right y) []       = That (y ◂ [])
{-# COMPILE AGDA2HS partitionEither #-}

--------------------------------------------------------------------------------
-- Decidable relations

_≟_ : {a : Set} ⦃ _ : Eq a ⦄ ⦃ @0 _ : IsLawfulEq a ⦄ → (x y : a) → Dec (x ≡ y)
x ≟ y = (x == y) ⟨ isEquality x y ⟩
{-# COMPILE AGDA2HS _≟_ inline #-}

ifDec : {@0 a : Set} {b : Set} → Dec a → (@0 ⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
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

@0 theseReflects : ∀ {ba bb a b} → Reflects a ba → Reflects b bb → Reflects (These a b) (ba || bb)
theseReflects {True}  {True}  a  b  = Both a b
theseReflects {True}  {False} a  ¬b = This a
theseReflects {False} {True}  ¬a b  = That b
theseReflects {False} {False} ¬a ¬b = these ¬a ¬b (λ a _ → ¬a a)

theseDec : ∀ {@0 a b} → Dec a → Dec b → Dec (These a b)
theseDec (ba ⟨ a ⟩) (bb ⟨ b ⟩) = (ba || bb) ⟨ theseReflects a b ⟩
{-# COMPILE AGDA2HS theseDec inline #-}

anyDec : ∀ {a} {@0 p : @0 a → Set}
  → (∀ x → Dec (p x))
  → (∀ xs → Dec (Any p xs))
anyDec f []       = False ⟨ (λ ()) ⟩
anyDec f (x ∷ xs) =
  mapDec
    (either here there)
    (λ where
      (here h)  → Left h
      (there h) → Right h)
    (eitherDec (f x) (anyDec f xs))
{-# COMPILE AGDA2HS anyDec #-}

firstDec : ∀ {a} {@0 p : @0 a → Set}
  → (∀ x → Dec (p x))
  → (∀ xs → Dec (First p xs))
firstDec         f []       = False ⟨ (λ ()) ⟩
firstDec {p = p} f (x ∷ xs) = ifDec (f x)
  (λ ⦃ h ⦄ → True ⟨ [ h ] ⟩)
  (λ ⦃ h ⦄ → mapDec (h ◂_) (lem h) (firstDec f xs))
  where
    @0 lem : ¬ p x → First p (x ∷ xs) → First p xs
    lem h [ h' ]   = contradiction h' h
    lem h (x ◂ h') = h'
{-# COMPILE AGDA2HS firstDec #-}

--------------------------------------------------------------------------------
-- Decidable relation that does not erase positive information

infix 3 tupleDecP

data DecP (a : Set) : Set where
  Yes : (p : a) → DecP a
  No  : (@0 p : ¬ a) → DecP a
{-# COMPILE AGDA2HS DecP deriving Show #-}

decPToDec : ∀ {a} → DecP a → Dec a
decPToDec (Yes p) = True ⟨ p ⟩
decPToDec (No p)  = False ⟨ p ⟩
{-# COMPILE AGDA2HS decPToDec #-}

decToDecP : ∀ {a} → Dec a → DecP (Erase a)
decToDecP (True ⟨ p ⟩)  = Yes (Erased p)
decToDecP (False ⟨ p ⟩) = No λ (Erased x) → p x
{-# COMPILE AGDA2HS decToDecP #-}

mapDecP : ∀ {a b} → (a → b) → @0 (b → a) → DecP a → DecP b
mapDecP f g (Yes p) = Yes (f p)
mapDecP f g (No p)  = No (contraposition g p)
{-# COMPILE AGDA2HS mapDecP #-}

ifDecP : {a b : Set} → DecP a → (⦃ a ⦄ → b) → (@0 ⦃ ¬ a ⦄ → b) → b
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

theseDecP : ∀ {a b} → DecP a → DecP b → DecP (These a b)
theseDecP (Yes p) (Yes q) = Yes (Both p q)
theseDecP (Yes p) (No q)  = Yes (This p)
theseDecP (No p)  (Yes q) = Yes (That q)
theseDecP (No p)  (No q)  = No (these p q (λ a _ → p a))
{-# COMPILE AGDA2HS theseDecP #-}

firstDecP : ∀ {a} {p : @0 a → Set}
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
