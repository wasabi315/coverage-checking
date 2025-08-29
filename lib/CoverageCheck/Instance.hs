module CoverageCheck.Instance where

import Control.Arrow (first)
import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Cons, Nil), Any, DecP(No, Yes), First, HAll2(HCons, HNil), eitherDecP, firstDecP, hAppend, hUnappend, mapDecP, tupleDecP)
import CoverageCheck.Syntax (Pattern(PCon, POr, PWild), Patterns, Tys, Value(VCon), Values, pWilds)

data Instance = IWild
              | ICon Name Instances
              | IOrL Instance
              | IOrR Instance
                  deriving Show

infix 4 `Instances`
type Instances = HAll2 Instance

infix 4 `InstanceMatrix`
type InstanceMatrix = Any Instances

iWilds :: Tys -> Instances
iWilds [] = HNil
iWilds (α : αs) = HCons IWild (iWilds αs)

iOrInv :: Instance -> Either Instance Instance
iOrInv (IOrL h) = Left h
iOrInv (IOrR h) = Right h

iConInv :: Instance -> Instances
iConInv (ICon c is) = is

iUncons :: Instances -> (Instance, Instances)
iUncons (HCons i is) = (i, is)

splitInstances :: Tys -> Values -> (Values, Values)
splitInstances [] us = (Nil, us)
splitInstances (α : αs) (Cons u us)
  = first (Cons u) (splitInstances αs us)

wildHeadLemma :: Tys -> Instances -> Instances
wildHeadLemma βs h
  = case hUnappend (pWilds βs) h of
        (_, h') -> HCons IWild h'

wildHeadLemmaInv :: Tys -> Instances -> Instances
wildHeadLemmaInv βs (HCons IWild h) = hAppend (iWilds βs) h

orHeadLemma :: Either Instances Instances -> Instances
orHeadLemma (Left (HCons h hs)) = HCons (IOrL h) hs
orHeadLemma (Right (HCons h hs)) = HCons (IOrR h) hs

orHeadLemmaInv :: Instances -> Either Instances Instances
orHeadLemmaInv (HCons (IOrL h) hs) = Left (HCons h hs)
orHeadLemmaInv (HCons (IOrR h) hs) = Right (HCons h hs)

conHeadLemma :: Name -> Patterns -> Instances -> Instances
conHeadLemma c rs h
  = case hUnappend rs h of
        (h1, h2) -> HCons (ICon c h1) h2

conHeadLemmaInv :: Patterns -> Instances -> Instances
conHeadLemmaInv rs (HCons (ICon c h) h') = hAppend h h'

infix 4 `decInstance`
decInstance :: Pattern -> Value -> DecP Instance
decInstance PWild v = Yes IWild
decInstance (POr p q) v
  = mapDecP (either IOrL IOrR)
      (eitherDecP (decInstance p v) (decInstance q v))
decInstance (PCon c ps) (VCon c' vs)
  = if c == c' then mapDecP (ICon c) (decInstances ps vs) else No

infix 4 `decInstances`
decInstances :: Patterns -> Values -> DecP Instances
decInstances Nil Nil = Yes HNil
decInstances (Cons p ps) (Cons v vs)
  = mapDecP (uncurry HCons)
      (tupleDecP (decInstance p v) (decInstances ps vs))

type Match = First Instances

decMatch :: [Patterns] -> Values -> DecP Match
decMatch p vs = firstDecP (\ ps -> decInstances ps vs) p

