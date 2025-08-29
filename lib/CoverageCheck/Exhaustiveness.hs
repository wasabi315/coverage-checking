{-# LANGUAGE LambdaCase #-}
module CoverageCheck.Exhaustiveness where

import CoverageCheck.Prelude (All(Nil, (:>)), NonEmpty, ifDecP)
import CoverageCheck.Syntax (Pattern, Patterns, Signature, Ty, Tys, Value, pWilds)
import CoverageCheck.Usefulness.Algorithm (decUseful)
import CoverageCheck.Usefulness.UsefulP (UsefulP(witnesses))

decNonExhaustive ::
                 Signature ->
                   (Ty -> Value) ->
                     Tys -> [Patterns] -> Either () (NonEmpty (All Pattern))
decNonExhaustive sig nonEmptyAxiom αs pss
  = ifDecP (decUseful sig nonEmptyAxiom αs pss (pWilds αs))
      (\ h ->
         Right
           (fmap
              (\case
                   qs :> Nil -> qs)
              (witnesses h)))
      (Left ())

