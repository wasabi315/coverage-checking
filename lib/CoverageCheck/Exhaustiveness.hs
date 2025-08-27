{-# LANGUAGE LambdaCase #-}
module CoverageCheck.Exhaustiveness where

import CoverageCheck.Prelude (NonEmpty, ifDecP)
import CoverageCheck.Syntax (Patterns, Signature, Ty, Tys, Value, pWilds)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import CoverageCheck.Usefulness.UsefulP (UsefulP(MkUsefulP))

decNonExhaustive ::
                 Signature ->
                   (Ty -> Value) -> Tys -> [Patterns] -> Either () (NonEmpty Patterns)
decNonExhaustive sig nonEmptyAxiom αs pss
  = ifDecP (decUseful sig nonEmptyAxiom αs pss (pWilds αs))
      (\ h ->
         Right
           ((\case
                 MkUsefulP hs -> hs)
              h))
      (Left ())

