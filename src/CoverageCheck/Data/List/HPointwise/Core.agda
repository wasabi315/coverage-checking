module CoverageCheck.Data.List.HPointwise.Core where

open import Haskell.Prelude hiding (All; a)

open import CoverageCheck.Data.List.All.Core

infixr 5 _:>>_

private
  variable
    @0 a : Type
    @0 p q : @0 a → Type
    r : ∀ {@0 x} → @0 p x → @0 q x → Type
    @0 x : a
    @0 xs : List a

--------------------------------------------------------------------------------

data HPointwise
  {@0 a : Type} {@0 p q : @0 a → Type}
  (r : ∀ {@0 x} → @0 p x → @0 q x → Type)
  : ∀ {@0 xs} → @0 All p xs → @0 All q xs → Type
  where
  HNil  : HPointwise r Nil Nil
  _:>>_ : ∀ {@0 x xs}
    → {@0 px : p x} {@0 pxs : All p xs}
    → {@0 qx : q x} {@0 qxs : All q xs}
    → r px qx
    → HPointwise r pxs qxs
    → HPointwise r (px :> pxs) (qx :> qxs)

{-# COMPILE AGDA2HS HPointwise deriving (Eq, Show) #-}
