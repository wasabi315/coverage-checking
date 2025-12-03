open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness

open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_)

module CoverageCheck.Exhaustiveness
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    αs : Tys
    @0 αs0 : Tys

--------------------------------------------------------------------------------
-- Exhaustiveness

module _ ⦃ @0 sig : Signature ⦄ where

  -- There is a matching row in P for every list of values
  Exhaustive : PatternMatrix αs0 → Type
  Exhaustive P = ∀ vs → Match P vs

  -- There is a list of patterns that has at least one instance and whose instances do not match any row in P
  NonExhaustive' : PatternMatrix αs0 → Type
  NonExhaustive' P = ∃[ ps ∈ _ ] ∀ {vs} → ps ≼* vs → ¬ Match P vs
  {-# COMPILE AGDA2HS NonExhaustive' inline #-}

  NonExhaustive : PatternMatrix αs0 → Type
  NonExhaustive P = NonEmpty (NonExhaustive' P)
  {-# COMPILE AGDA2HS NonExhaustive inline #-}

  -- non-exhaustiveness defined in terms of usefulness:
  -- P is non-exhaustive if —* is useful with respect to P
  NonExhaustiveU : PatternMatrix αs0 → Type
  NonExhaustiveU P = Useful P —*
  {-# COMPILE AGDA2HS NonExhaustiveU inline #-}

  -- P is exhaustive if —* is not useful with respect to P
  ExhaustiveU : PatternMatrix αs0 → Type
  ExhaustiveU P = ¬ NonExhaustiveU P

  module _ {@0 P : PatternMatrix αs0} where

    nonExhaustiveUToNonExhaustive' : Useful' P —* → NonExhaustive' P
    nonExhaustiveUToNonExhaustive' ⟪ qs , disj , _ ⟫ =
      qs ⟨ (λ is ms → disj (First⇒Any ms) is) ⟩
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive' transparent #-}

    nonExhaustiveUToNonExhaustiveList : List (Useful' P —*) → List (NonExhaustive' P)
    nonExhaustiveUToNonExhaustiveList [] = []
    nonExhaustiveUToNonExhaustiveList (h ∷ hs) =
      nonExhaustiveUToNonExhaustive' h ∷ nonExhaustiveUToNonExhaustiveList hs
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustiveList transparent #-}

    nonExhaustiveUToNonExhaustive : NonEmpty (Useful' P —*) → NonExhaustive P
    nonExhaustiveUToNonExhaustive (h ∷ hs) =
      nonExhaustiveUToNonExhaustive' h ∷ nonExhaustiveUToNonExhaustiveList hs
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive transparent #-}

    @0 nonExhaustiveToNonExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → NonExhaustive P
      → NonExhaustiveU P
    nonExhaustiveToNonExhaustiveU hs = record
      { witnesses = flip fmap hs λ (qs ⟨ h ⟩) →
          ⟪ qs , (λ iss is → ¬First⇒¬Any (h is) iss) , —⊆* ⟫
      }

    @0 exhaustiveToExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → Exhaustive P
      → ExhaustiveU P
    exhaustiveToExhaustiveU h u
      using ⟪ qs , disj , _ ⟫ ∷ _ ← u .witnesses
      = contradiction (First⇒Any (h (examplesFor qs))) (flip disj (examplesFor≼ qs))


  module @0 _ {P : PatternMatrix αs0} where

    exhaustiveUToExhaustive : ExhaustiveU P → Exhaustive P
    exhaustiveUToExhaustive h vs =
      case decMatch P vs of λ where
        (Yes h') → h'
        (No h')  →
          contradiction
            (record
              { witnesses =
                  ⟪ onlys vs
                  , (λ iss is →
                      ¬First⇒¬Any h'
                        (subst (λ vs → P ≼** vs) (sym (onlys≼⇒≡ is)) iss))
                  , —⊆* ⟫ ∷ []
              })
            h

--------------------------------------------------------------------------------
-- Entrypoint

module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  decExhaustive : (pss : PatternMatrix αs)
    → Either (NonExhaustive pss) (Erase (Exhaustive pss))
  decExhaustive pss = ifDecP (decUseful pss pWilds)
    (λ ⦃ h ⦄ → Left (nonExhaustiveUToNonExhaustive (h .witnesses)))
    (λ ⦃ h ⦄ → Right (Erased (exhaustiveUToExhaustive h)))
  {-# COMPILE AGDA2HS decExhaustive #-}
