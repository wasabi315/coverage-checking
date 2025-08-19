open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness

module CoverageCheck.Exhaustiveness
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Exhaustiveness

module _ ⦃ @0 sig : Signature ⦄ where

  -- There is a matching row in P for every list of values
  Exhaustive : PatternMatrix αs0 → Type
  Exhaustive P = ∀ vs → Match P vs

  -- There is a list of values that does not match any row in P
  NonExhaustive : PatternMatrix αs0 → Type
  NonExhaustive P = ∃[ vs ∈ _ ] ¬ Match P vs
  {-# COMPILE AGDA2HS NonExhaustive inline #-}

  -- non-exhaustiveness defined in terms of usefulness:
  -- P is non-exhaustive if —* is useful with respect to P
  NonExhaustive' : PatternMatrix αs0 → Type
  NonExhaustive' P = Useful P —*
  {-# COMPILE AGDA2HS NonExhaustive' inline #-}

  -- P is exhaustive if —* is not useful with respect to P
  Exhaustive' : PatternMatrix αs0 → Type
  Exhaustive' P = ¬ NonExhaustive' P

  module _ {@0 P : PatternMatrix αs0} where

    nonExhaustive'ToNonExhaustive : NonExhaustive' P → NonExhaustive P
    nonExhaustive'ToNonExhaustive = λ where
      (MkUseful vs nis _) → vs ⟨ contraposition firstToAny nis ⟩
    {-# COMPILE AGDA2HS nonExhaustive'ToNonExhaustive inline #-}

    nonExhaustiveToNonExhaustive' : NonExhaustive P → NonExhaustive' P
    nonExhaustiveToNonExhaustive' (vs ⟨ h ⟩) =
      MkUseful vs (notFirstToNotAny h) —≼*

    exhaustiveToExhaustive' : Exhaustive P → Exhaustive' P
    exhaustiveToExhaustive' h (MkUseful vs nis _) =
      contradiction (firstToAny (h vs)) nis


  module _ {P : PatternMatrix αs0} where

    exhaustive'ToExhaustive : Exhaustive' P → Exhaustive P
    exhaustive'ToExhaustive h vs =
      case decMatch P vs of λ where
        (Yes h') → h'
        (No h')  → contradiction (MkUseful vs (notFirstToNotAny h') —≼*) h

--------------------------------------------------------------------------------
-- Entrypoint

module _ ⦃ sig : Signature ⦄ ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  decNonExhaustive : (pss : PatternMatrix αs) → Either (Erase (Exhaustive pss)) (NonExhaustive pss)
  decNonExhaustive pss = ifDecP (decUsefulTerm (λ ⦃ sig' ⦄ → Useful ⦃ sig = sig' ⦄) pss pWilds)
    (λ ⦃ h ⦄ → Right (nonExhaustive'ToNonExhaustive h))
    (λ ⦃ h ⦄ → Left (Erased (exhaustive'ToExhaustive h)))
  {-# COMPILE AGDA2HS decNonExhaustive #-}
