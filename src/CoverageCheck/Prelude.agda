module CoverageCheck.Prelude where

--------------------------------------------------------------------------------
-- agda2hs re-exports

open import Haskell.Prim public
  using (⊥)
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
         Σ0; ⟨_⟩_; <_>;
         Rezz; rezz; rezzCong; rezzCong2)

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
  using (sum; map; _++_; concatMap; length)


-- open import Data.List.Relation.Unary.All public
--   using (All; []; _∷_)
--   renaming (head to headAll; tail to tailAll; tabulate to tabulateAll)
-- open import Data.List.Relation.Unary.All.Properties public
  -- using (¬All⇒Any¬; All¬⇒¬Any; ¬Any⇒All¬)

-- open import Data.List.Relation.Unary.Any public
--   using (Any; here; there)
  -- renaming (map to mapAny)
-- open import Data.List.Relation.Unary.Any.Properties public
--   using ()
  -- renaming (gmap to gmapAny; concat⁺ to concatAny⁺; concat⁻ to concatAny⁻;
  --           ++⁻ to ++Any⁻; ++⁺ˡ to ++Any⁺ˡ; ++⁺ʳ to ++Any⁺ʳ; map⁻ to mapAny⁻)

-- open import Data.List.Relation.Unary.First public
--   using (First; _∷_; [_])
  -- renaming (toAny to First⇒Any)
-- open import Data.List.Relation.Unary.First.Properties public
--   using (All⇒¬First)

--------------------------------------------------------------------------------
-- Equality

cong0 : {@0 a : Set} {b : Set} {@0 x y : a} (f : a → b) → @0 x ≡ y → f x ≡ f y
cong0 f refl = refl

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

@0 ¬Any⇒All¬ : {a : Set} {p : @0 a → Set} (xs : List a)
  → ¬ Any p xs
  → All (λ x → ¬ p x) xs
¬Any⇒All¬ []       ¬p = ⌈⌉
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ◂ ¬Any⇒All¬ xs (¬p ∘ there)

data First {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  FirstHere  : ∀ {@0 x xs} → p x → First p (x ∷ xs)
  FirstThere : ∀ {@0 x xs} → @0 ¬ p x → First p xs → First p (x ∷ xs)

{-# COMPILE AGDA2HS First deriving Show #-}

pattern [_] h    = FirstHere h
pattern _◂_ h hs = FirstThere h hs

@0 Fresh : {a : Set} → List a → Set
Fresh []       = ⊤
Fresh (x ∷ xs) = All (λ y → ¬ x ≡ y) xs × Fresh xs

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

--------------------------------------------------------------------------------

-- open import Data.Empty public
--   using (⊥; ⊥-elim)

-- open import Data.Fin.Base public
--   using (Fin; zero; suc)
-- open import Data.Fin.Properties public
--   using (¬Fin0)
--   renaming (_≟_ to _≟Fin_; any? to anyFin?)

-- open import Data.List.Base public
--   using (List; []; _∷_; _++_; concatMap; length)
--   renaming (sum to sumList; map to mapList)
-- open import Data.List.Properties public
--   using (sum-++; map-++; ++-identityʳ)

-- open import Data.List.Relation.Unary.All public
--   using (All; []; _∷_)
--   renaming (head to headAll; tail to tailAll; tabulate to tabulateAll)
-- open import Data.List.Relation.Unary.All.Properties public
--   using (¬All⇒Any¬; All¬⇒¬Any; ¬Any⇒All¬)
--   renaming (++⁺ to ++All⁺)

-- open import Data.List.Relation.Unary.Any public
--   using (Any; here; there; any?)
--   renaming (map to mapAny)
-- open import Data.List.Relation.Unary.Any.Properties public
--   using (¬Any[])
--   renaming (gmap to gmapAny; concat⁺ to concatAny⁺; concat⁻ to concatAny⁻;
--             ++⁻ to ++Any⁻; ++⁺ˡ to ++Any⁺ˡ; ++⁺ʳ to ++Any⁺ʳ; map⁻ to mapAny⁻)

-- open import Data.List.Relation.Unary.First public
--   using (First; _∷_)
--   renaming (toAny to First⇒Any)
-- open import Data.List.Relation.Unary.First.Properties public
--   using (All⇒¬First)
--   renaming (cofirst? to first?)

-- open import Data.Product.Base public
--   using (∃-syntax; _×_; -,_; _,_; uncurry; proj₁; proj₂)
--   renaming (map to map-×; map₁ to map-×₁; map₂ to map-×₂)
-- open import Data.Product.Relation.Binary.Lex.Strict public
--   using (×-Lex; ×-wellFounded)

-- open import Data.Sum.Base public
--   using (_⊎_; inj₁; inj₂; [_,_])
--   renaming (map to map-⊎)

-- open import Function.Base public
--   using (id; _∘_; flip; _on_)

-- open import Function.Bundles public
--   using (_⇔_; mk⇔)

-- open import Induction.WellFounded public
--   using (WellFounded; Acc; acc)

-- open import Relation.Binary.Construct.On public
--   using ()
--   renaming (wellFounded to on-wellFounded)

-- open import Relation.Binary.PropositionalEquality.Core public
--   using (_≡_; _≢_; refl; sym; ≢-sym; trans; cong; cong₂)

-- open import Relation.Nullary.Decidable public
--   using (Dec; yes; no; ¬?; _⊎-dec_; _×-dec_)
--   renaming (map to mapDec; map′ to mapDec′)

-- open import Relation.Nullary.Negation.Core public
--   using (¬_; contradiction; contraposition)

-- -- extra lemmas

-- module _ where
--   open import Data.Empty using (⊥-elim)
--   open import Data.Fin.Properties using (∀-cons)
--   open import Data.List.Relation.Unary.First using ([_])
--   open import Relation.Unary using (Pred; ∁; _⊆_; Decidable)
--   open import Relation.Nullary.Decidable.Core using (toSum)

--   ¬First⇒¬Any : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
--     → ∁ Q ⊆ P
--     → ∁ (First P Q) ⊆ ∁ (Any Q)
--   ¬First⇒¬Any ¬q⇒p ¬pqxxs (here qx) = ¬pqxxs [ qx ]
--   ¬First⇒¬Any ¬q⇒p ¬pqxxs (there qxs) =
--     ¬First⇒¬Any ¬q⇒p (¬pqxxs ∘ (¬q⇒p (¬pqxxs ∘ [_]) ∷_)) qxs

--   allOrCounterexample : ∀ {p n} {P : Fin n → Set p}
--     → Decidable P
--     → (∀ x → P x) ⊎ (∃[ x ] ¬ P x)
--   allOrCounterexample {n = zero} P? = inj₁ (⊥-elim ∘ ¬Fin0)
--   allOrCounterexample {n = suc n} P? with P? zero
--   ... | no ¬P0 = inj₂ (zero , ¬P0)
--   ... | yes P0 =
--         map-⊎ (∀-cons P0) (map-× suc id) (allOrCounterexample (P? ∘ suc))
