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

  -- There is a matching row in P for any list of values
  Exhaustive : PatternMatrix αs0 → Type
  Exhaustive pmat = ∀ vs → FirstMatch vs pmat

  -- There is a list of patterns that has at least one instance and whose instances do not match any row in P
  NonExhaustive' : PatternMatrix αs0 → Type
  NonExhaustive' pmat = ∃[ ps ∈ _ ] ∀ {vs} → vs ≼* ps → ¬ FirstMatch vs pmat
  {-# COMPILE AGDA2HS NonExhaustive' inline #-}

  NonExhaustive : PatternMatrix αs0 → Type
  NonExhaustive pmat = NonEmpty (NonExhaustive' pmat)
  {-# COMPILE AGDA2HS NonExhaustive inline #-}

  -- Non-exhaustiveness defined in terms of usefulness:
  -- P is non-exhaustive if —* is useful with respect to P
  NonExhaustiveU : PatternMatrix αs0 → Type
  NonExhaustiveU pmat = Useful pmat —*
  {-# COMPILE AGDA2HS NonExhaustiveU inline #-}

  -- P is exhaustive if —* is not useful with respect to P
  ExhaustiveU : PatternMatrix αs0 → Type
  ExhaustiveU pmat = ¬ NonExhaustiveU pmat

  module _ {@0 pmat : PatternMatrix αs0} where

    nonExhaustiveUToNonExhaustive' : Useful' pmat —* → NonExhaustive' pmat
    nonExhaustiveUToNonExhaustive' ⟪ qs , disj , _ ⟫ =
      qs ⟨ (λ insts matches → disj (First⇒Any matches) insts) ⟩
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive' transparent #-}

    nonExhaustiveUToNonExhaustiveList : List (Useful' pmat —*) → List (NonExhaustive' pmat)
    nonExhaustiveUToNonExhaustiveList [] = []
    nonExhaustiveUToNonExhaustiveList (h ∷ hs) =
      nonExhaustiveUToNonExhaustive' h ∷ nonExhaustiveUToNonExhaustiveList hs
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustiveList transparent #-}

    nonExhaustiveUToNonExhaustive : NonEmpty (Useful' pmat —*) → NonExhaustive pmat
    nonExhaustiveUToNonExhaustive (h ∷ hs) =
      nonExhaustiveUToNonExhaustive' h ∷ nonExhaustiveUToNonExhaustiveList hs
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive transparent #-}

    @0 nonExhaustiveToNonExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → NonExhaustive pmat
      → NonExhaustiveU pmat
    nonExhaustiveToNonExhaustiveU hs = record
      { witnesses = flip fmap hs λ (qs ⟨ h ⟩) →
          ⟪ qs , (λ instMat insts → ¬First⇒¬Any (h insts) instMat) , —⊆* ⟫
      }

    @0 exhaustiveToExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → Exhaustive pmat
      → ExhaustiveU pmat
    exhaustiveToExhaustiveU h u
      using ⟪ qs , disj , _ ⟫ ∷ _ ← u .witnesses
      = contradiction (First⇒Any (h (examplesFor qs))) (flip disj (examplesFor≼ qs))


  module @0 _ {pmat : PatternMatrix αs0} where

    exhaustiveUToExhaustive : ExhaustiveU pmat → Exhaustive pmat
    exhaustiveUToExhaustive h vs =
      case decPFirstMatch vs pmat of λ where
        (Yes h') → h'
        (No h')  →
          contradiction
            (record
              { witnesses =
                  ⟪ onlys vs
                  , (λ instMat insts →
                      ¬First⇒¬Any h'
                        (subst (λ vs → vs ≼ᵐ pmat) (onlys≼⇒≡ insts) instMat))
                  , —⊆* ⟫ ∷ []
              })
            h

--------------------------------------------------------------------------------
-- Entrypoint

module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  decExhaustive : (pmat : PatternMatrix αs)
    → Either (NonExhaustive pmat) (Erase (Exhaustive pmat))
  decExhaustive pmat = ifDecP (decPUseful pmat pWilds)
    (λ ⦃ h ⦄ → Left (nonExhaustiveUToNonExhaustive (h .witnesses)))
    (λ ⦃ h ⦄ → Right (Erased (exhaustiveUToExhaustive h)))
  {-# COMPILE AGDA2HS decExhaustive #-}
