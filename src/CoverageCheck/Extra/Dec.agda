module CoverageCheck.Extra.Dec where

open import Haskell.Prelude
open import Haskell.Extra.Refinement

open import CoverageCheck.Data.These
open import CoverageCheck.Extra.Negation

open import Haskell.Extra.Dec public hiding
  ( iDecIsTrue; iDecIsFalse; iDecPair; iDecEither )

--------------------------------------------------------------------------------

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

negDec : ∀ {@0 a : Type} → Dec a → Dec (¬ a)
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
dec-stable (False ⟨ ¬a ⟩) ¬¬a = undefined {i = ¬¬a ¬a}
