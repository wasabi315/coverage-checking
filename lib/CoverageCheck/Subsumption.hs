module CoverageCheck.Subsumption where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (HPointwise(HNil, (:>>)))
import CoverageCheck.Syntax (Tys)

data Subsumption = SWild
                 | SCon Name Subsumptions
                 | SOrL Subsumption
                 | SOrR Subsumption
                     deriving Show

infix 4 `Subsumptions`
type Subsumptions = HPointwise Subsumption

sWilds :: Tys -> Subsumptions
sWilds [] = HNil
sWilds (α : αs) = SWild :>> sWilds αs

sOrInv :: Subsumption -> Either Subsumption Subsumption
sOrInv (SOrL sub) = Left sub
sOrInv (SOrR sub) = Right sub

sConInv :: Subsumption -> Subsumptions
sConInv (SCon c subs) = subs

