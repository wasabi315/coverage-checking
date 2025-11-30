module CoverageCheck.Subsumption where

import CoverageCheck.Instance (Instance(ICon, IOrL, IOrR, IWild), Instances)
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
sOrInv (SOrL s) = Left s
sOrInv (SOrR s) = Right s

sConInv :: Subsumption -> Subsumptions
sConInv (SCon c ss) = ss

subsume :: Subsumption -> Instance -> Instance
subsume SWild i = IWild
subsume (SCon c ss) i = subsumeConCase ss i
subsume (SOrL s) i = IOrL (subsume s i)
subsume (SOrR s) i = IOrR (subsume s i)

subsumeConCase :: Subsumptions -> Instance -> Instance
subsumeConCase ss (ICon c is) = ICon c (subsumes ss is)

subsumes :: Subsumptions -> Instances -> Instances
subsumes HNil HNil = HNil
subsumes (s :>> ss) (i :>> is) = subsume s i :>> subsumes ss is

