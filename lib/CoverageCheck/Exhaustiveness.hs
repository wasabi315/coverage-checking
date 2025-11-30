module CoverageCheck.Exhaustiveness where

import CoverageCheck.Prelude (All, ifDecP)
import CoverageCheck.Syntax (Pattern, Patterns, Signature, Tys, pWilds)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import CoverageCheck.Usefulness.Definition (Useful(witnesses))
import Data.List.NonEmpty (NonEmpty((:|)))

decNonExhaustive ::
                 Signature ->
                   Tys -> [Patterns] -> Either () (NonEmpty (All Pattern))
decNonExhaustive sig αs pss
  = ifDecP (decUseful sig αs pss (pWilds αs))
      (\ h -> Right (witnesses h))
      (Left ())

