open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness
open import CoverageCheck.Usefulness.Algorithm

open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_)

module CoverageCheck.NonRedundancy
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    αs : Tys
    @0 αs0 : Tys

--------------------------------------------------------------------------------

module _ ⦃ @0 sig : Signature ⦄ where

  -- A pattern matrix satisfies AllNonRedundant if every row is useful
  -- with respect to all earlier rows.
  AllNonRedundant : @0 PatternMatrix αs0 → Type
  AllNonRedundant pmat =
    All
      (λ pmat' → Useful (NonEmpty.init pmat') (NonEmpty.last pmat'))
      (inits1 pmat)
  {-# COMPILE AGDA2HS AllNonRedundant inline #-}

  -- A predicate on pattern matrices that expresses the existence
  -- of redundant rows.
  -- This type compiles to one that is roughly isomorphic to List Bool, but it is
  -- guaranteed that at least one element is true.
  SomeRedundant : @0 PatternMatrix αs0 → Type
  SomeRedundant pmat =
    Some
      (λ pmat' → Erase (¬ Useful (NonEmpty.init pmat') (NonEmpty.last pmat')))
      (inits1 pmat)
  {-# COMPILE AGDA2HS SomeRedundant inline #-}


module @0 _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  -- The negation of SomeRedundant implies AllNonRedundant.
  ¬SomeRedundant→AllNonRedundant : (pmat : PatternMatrix αs)
    → ¬ SomeRedundant pmat
    → AllNonRedundant pmat
  ¬SomeRedundant→AllNonRedundant pmat h =
    mapAll
      (λ {pmat'} h → dec-stable (decUseful _ _) (h ∘ Erased))
      (¬Some⇒All¬ (inits1 pmat) h)

--------------------------------------------------------------------------------
-- Entrypoint

module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  -- Decides whether a pattern matrix satisfies non-redundancy.
  -- If it does not, we obtain a proof indicating which row is redundant.
  decAllNonRedundant : (pmat : PatternMatrix αs)
    → Either (SomeRedundant pmat) (Erase (AllNonRedundant pmat))
  decAllNonRedundant pmat =
    ifDecP
      (someDecP
        (λ pmat' →
          decToDecP
            (negDec (decUseful (NonEmpty.init pmat') (NonEmpty.last pmat'))))
        (inits1 pmat))
      (λ ⦃ h ⦄ → Left h)
      (λ ⦃ h ⦄ → Right (Erased (¬SomeRedundant→AllNonRedundant pmat h)))
  {-# COMPILE AGDA2HS decAllNonRedundant #-}
