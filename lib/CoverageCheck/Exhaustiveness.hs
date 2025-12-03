module CoverageCheck.Exhaustiveness where

import CoverageCheck.Prelude (All, ifDecP)
import CoverageCheck.Syntax (Pattern, Patterns, Signature, Tys, pWilds)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import CoverageCheck.Usefulness.Definition (Useful(witnesses))
import Data.List.NonEmpty (NonEmpty((:|)))

decExhaustive ::
              Signature ->
                Tys -> [Patterns] -> Either (NonEmpty (All Pattern)) ()
decExhaustive sig αs pmat
  = ifDecP (decUseful sig αs pmat (pWilds αs))
      (\ h -> Left (witnesses h))
      (Right ())

