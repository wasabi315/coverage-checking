module CoverageCheck.NonRedundancy where

import CoverageCheck.Prelude (Some, decToDecP, ifDecP, someDecP)
import CoverageCheck.Syntax (Patterns, Signature, Tys)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import Data.List (inits1)
import qualified Data.List.NonEmpty (init, last)

decAllNonRedundant ::
                   Signature -> Tys -> [Patterns] -> Either (Some ()) ()
decAllNonRedundant sig αs pmat
  = ifDecP
      (someDecP
         (\ pmat' ->
            decToDecP
              (not
                 (decUseful sig αs (Data.List.NonEmpty.init pmat')
                    (Data.List.NonEmpty.last pmat'))))
         (inits1 pmat))
      (\ h -> Left h)
      (Right ())

