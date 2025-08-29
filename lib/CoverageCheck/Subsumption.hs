module CoverageCheck.Subsumption where

import Control.Arrow (first)
import CoverageCheck.Instance (Instance(ICon, IOrL, IOrR, IWild), Instances(ICons, INil))
import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Cons, Nil))
import CoverageCheck.Syntax (Patterns, Tys)

data Subsumption = SWild
                 | SCon Name Subsumptions
                 | SOrL Subsumption
                 | SOrR Subsumption
                     deriving Show

data Subsumptions = SNil
                  | SCons Subsumption Subsumptions
                      deriving Show

sWilds :: Tys -> Subsumptions
sWilds [] = SNil
sWilds (α : αs) = SCons SWild (sWilds αs)

sOrInv :: Subsumption -> Either Subsumption Subsumption
sOrInv (SOrL s) = Left s
sOrInv (SOrR s) = Right s

sConInv :: Subsumption -> Subsumptions
sConInv (SCon c ss) = ss

infixr 5 `appendSubsumptions`
appendSubsumptions :: Subsumptions -> Subsumptions -> Subsumptions
appendSubsumptions SNil bs' = bs'
appendSubsumptions (SCons s ss) ss'
  = SCons s (appendSubsumptions ss ss')

unappendSubsumptions ::
                     Patterns -> Subsumptions -> (Subsumptions, Subsumptions)
unappendSubsumptions Nil bs = (SNil, bs)
unappendSubsumptions (Cons p ps) (SCons s ss)
  = first (SCons s) (unappendSubsumptions ps ss)

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
subsumes SNil INil = INil
subsumes (SCons s ss) (ICons i is)
  = ICons (subsume s i) (subsumes ss is)

