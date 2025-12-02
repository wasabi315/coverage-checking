module Haskell.Data.List.NonEmpty where

open import Haskell.Prim using (Type; List; []; _∘_)
open import Haskell.Prim.Applicative using (Applicative; pure; _<*>_; DefaultApplicative)
open import Haskell.Prim.Functor using (Functor; fmap; _<$_)
open import Haskell.Prim.List using (_++_)
open import Haskell.Prim.Monad using (Monad; _>>=_; DefaultMonad)
open import Haskell.Prim.Monoid using (Semigroup; _<>_)

infixr 5 _:|_ _∷_ _<|_

--------------------------------------------------------------------------------

record NonEmpty (a : Type) : Type where
  no-eta-equality
  pattern
  constructor _:|_
  field
    head : a
    tail : List a

open NonEmpty public

pattern _∷_ x xs = x :| xs

toList : {a : Type} → NonEmpty a → List a
toList xs = head xs List.∷ tail xs

_<|_ : {a : Type} → a → NonEmpty a → NonEmpty a
x <| xs = x ∷ head xs List.∷ tail xs

cons = _<|_

singleton : {a : Type} → a → NonEmpty a
singleton x = x ∷ []

--------------------------------------------------------------------------------

private
  bindNonEmpty : ∀ {a b} → NonEmpty a → (a → NonEmpty b) → NonEmpty b
  bindNonEmpty xs f = head fx ∷ tail fx ++ fxs
    where
      fx = f (head xs)
      fxs = tail xs >>= (toList ∘ f)

instance

  iFunctorNonEmpty : Functor NonEmpty
  iFunctorNonEmpty .fmap f xs = f (head xs) ∷ fmap f (tail xs)
  iFunctorNonEmpty ._<$_ b xs = b ⦃ head xs ⦄ ∷ (b <$ tail xs)

  iDefaultApplicativeNonEmpty : DefaultApplicative NonEmpty
  iDefaultApplicativeNonEmpty .DefaultApplicative.pure x = x ∷ []
  iDefaultApplicativeNonEmpty .DefaultApplicative._<*>_ fs xs =
    bindNonEmpty fs λ f → bindNonEmpty xs λ x → f x ∷ []

  iApplicativeNonEmpty : Applicative NonEmpty
  iApplicativeNonEmpty = record {DefaultApplicative iDefaultApplicativeNonEmpty}

  iDefaultMonadNonEmpty : DefaultMonad NonEmpty
  iDefaultMonadNonEmpty .DefaultMonad._>>=_ = bindNonEmpty

  iMonadNonEmpty : Monad NonEmpty
  iMonadNonEmpty = record {DefaultMonad iDefaultMonadNonEmpty}

  iSemigroupNonEmpty : ∀ {a} → Semigroup (NonEmpty a)
  iSemigroupNonEmpty ._<>_ (x ∷ xs) ys = x ∷ xs ++ toList ys
