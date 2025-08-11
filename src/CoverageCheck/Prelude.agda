module CoverageCheck.Prelude where

--------------------------------------------------------------------------------
-- Re-exports

open import Haskell.Prim public
  using (⊥; exFalso)
open import Haskell.Prim.Tuple public
  using (first; second)

open import Haskell.Prelude public
  using (id; _∘_; flip; case_of_;
         Bool; True; False;
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
  using (IsLawfulEq; isEquality; _≟_)

open import Haskell.Law.Equality public
  using (cong; cong₂; subst0)

open import Haskell.Extra.Dec public
  using (Reflects; mapReflects; invert; extractFalse)
  renaming (Dec to Dec0; mapDec to mapDec0; ifDec to ifDec0)

open import Haskell.Extra.Erase public
  using (Erase; Erased; get;
         Σ0; ⟨_⟩_; <_>;
         Rezz; rezz; rezzCong; rezzCong2)

Σ0-syntax = Σ0
{-# COMPILE AGDA2HS Σ0-syntax inline #-}
syntax Σ0-syntax A (λ x → B) = Σ0[ x ∈ A ] B
infix 2 Σ0-syntax

open import Haskell.Extra.Refinement public
  using (∃; _⟨_⟩)

∃-syntax = ∃
{-# COMPILE AGDA2HS ∃-syntax inline #-}
syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 2 ∃-syntax

open import Haskell.Extra.Sigma public
  using (Σ-syntax; _,_; fst; snd)

--------------------------------------------------------------------------------
-- Predicates on lists

infixr 5 _◂_

data Any {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  AnyHere  : ∀ {@0 x xs} → p x → Any p (x ∷ xs)
  AnyThere : ∀ {@0 x xs} → Any p xs → Any p (x ∷ xs)
{-# COMPILE AGDA2HS Any deriving Show #-}

pattern here  x    = AnyHere x
pattern there x xs = AnyThere x xs

data All {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  AllNil  : All p []
  AllCons : ∀ {@0 x xs} → p x → All p xs → All p (x ∷ xs)
{-# COMPILE AGDA2HS All deriving Show #-}

pattern ⌈⌉       = AllNil
pattern _◂_ p ps = AllCons p ps

data First {@0 a : Set} (p : @0 a → Set) : (@0 xs : List a) → Set where
  FirstHere  : ∀ {@0 x xs} → p x → First p (x ∷ xs)
  FirstThere : ∀ {@0 x xs} → @0 (p x → ⊥) → First p xs → First p (x ∷ xs)
{-# COMPILE AGDA2HS First deriving Show #-}

pattern ⌈_⌉ x    = FirstHere x
pattern _◂_ x xs = FirstThere x xs

--------------------------------------------------------------------------------
-- Negation

exFalso0 : {a : Set} → @0 ⊥ → a
exFalso0 _ = undefined

contradiction : {a b : Set} → a → @0 (a → ⊥) → b
contradiction a ¬a = exFalso0 (¬a a)

contraposition : {a b : Set} → (a → b) → (b → ⊥) → (a → ⊥)
contraposition f g = g ∘ f

--------------------------------------------------------------------------------
-- Decidable

infix 3 tupleDec

data Dec (a : Set) : Set where
  Yes : (p : a) → Dec a
  No  : (@0 p : a → ⊥) → Dec a
{-# COMPILE AGDA2HS Dec deriving Show #-}

mapDec : ∀ {a b} → (a → b) → @0 (b → a) → Dec a → Dec b
mapDec f g (Yes p) = Yes (f p)
mapDec f g (No p)  = No (contraposition g p)
{-# COMPILE AGDA2HS mapDec #-}

tupleDec : ∀ {a b} → Dec a → Dec b → Dec (a × b)
syntax tupleDec a b = a ×-dec b
No p  ×-dec _     = No (contraposition fst p)
Yes _ ×-dec No q  = No (contraposition snd q)
Yes p ×-dec Yes q = Yes (p , q)
{-# COMPILE AGDA2HS tupleDec #-}

eitherDec : ∀ {a b} → Dec a → Dec b → Dec (Either a b)
eitherDec (Yes p) _       = Yes (Left p)
eitherDec (No p)  (Yes q) = Yes (Right q)
eitherDec (No p)  (No q)  = No (either p q)
{-# COMPILE AGDA2HS eitherDec #-}

firstDec : {a : Set} {p : @0 a → Set}
  → (∀ x → Dec (p x))
  → ∀ xs → Dec (First p xs)
firstDec f []       = No (λ _ → undefined)
firstDec f (x ∷ xs) = case f x of λ
  { (Yes p) → Yes ⌈ p ⌉
  ; (No p)  → mapDec (p ◂_) (λ { ⌈ h ⌉ → contradiction h p; (_ ◂ h) → h }) (firstDec f xs)
  }
{-# COMPILE AGDA2HS firstDec #-}

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

-- open import Data.Nat.Base public
--   using (ℕ; zero; suc; _+_; _≤_; _<_; s<s)
-- open import Data.Nat.Induction public
--   using (<-wellFounded)
-- open import Data.Nat.Properties public
--   using (+-identityʳ;
--          ≤-refl; module ≤-Reasoning; +-mono-≤; n≤1+n;
--          n<1+n; 0<1+n; <⇒≤; +-monoˡ-<; +-monoʳ-<;
--          +-mono-<-≤; +-mono-≤-<; m≤n⇒m<n∨m≡n; m≤m+n; m≤n+m)

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
