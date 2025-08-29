module CoverageCheck.Exhaustiveness where

import CoverageCheck.Prelude (All, NonEmpty(MkNonEmpty), ifDecP)
import CoverageCheck.Syntax (Pattern, Patterns, Signature, Ty, Tys, Value, pWilds)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import CoverageCheck.Usefulness.UsefulP (UsefulP(witnesses))

decNonExhaustive ::
                 Signature ->
                   (Ty -> Value) ->
                     Tys -> [Patterns] -> Either () (NonEmpty (All Pattern))
decNonExhaustive sig nonEmptyAxiom αs pss
  = ifDecP (decUseful sig nonEmptyAxiom αs pss (pWilds αs))
      (\ h -> Right (witnesses h))
      (Left ())

