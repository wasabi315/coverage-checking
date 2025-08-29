module CoverageCheck.Subsumption where

import Control.Arrow (first)
import CoverageCheck.Instance (Instance(ICon, IOrL, IOrR, IWild), Instances)
import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Cons, Nil), HAll2(HCons, HNil))
import CoverageCheck.Syntax (Patterns, Tys)

data Subsumption = SWild
                 | SCon Name Subsumptions
                 | SOrL Subsumption
                 | SOrR Subsumption
                     deriving Show

infix 4 `Subsumptions`
type Subsumptions = HAll2 Subsumption

sWilds :: Tys -> Subsumptions
sWilds [] = HNil
sWilds (α : αs) = HCons SWild (sWilds αs)

sOrInv :: Subsumption -> Either Subsumption Subsumption
sOrInv (SOrL s) = Left s
sOrInv (SOrR s) = Right s

sConInv :: Subsumption -> Subsumptions
sConInv (SCon c ss) = ss

splitSubsumptions :: Tys -> Patterns -> (Patterns, Patterns)
splitSubsumptions [] rs = (Nil, rs)
splitSubsumptions (α : αs) (Cons r rs)
  = first (Cons r) (splitSubsumptions αs rs)

subsume :: Subsumption -> Instance -> Instance
subsume SWild i = IWild
subsume (SCon c ss) i = subsumeConCase ss i
subsume (SOrL s) i = IOrL (subsume s i)
subsume (SOrR s) i = IOrR (subsume s i)

subsumeConCase :: Subsumptions -> Instance -> Instance
subsumeConCase ss (ICon c is) = ICon c (subsumes ss is)

subsumes :: Subsumptions -> Instances -> Instances
subsumes HNil HNil = HNil
subsumes (HCons s ss) (HCons i is)
  = HCons (subsume s i) (subsumes ss is)

