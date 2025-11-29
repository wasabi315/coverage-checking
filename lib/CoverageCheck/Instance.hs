module CoverageCheck.Instance where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Nil, (:>)), Any, DecP(No, Yes), First, HAll2(HNil, (:>>)), eitherDecP, firstDecP, mapDecP, tupleDecP)
import CoverageCheck.Syntax (Pattern(PCon, POr, PWild), Patterns, Tys, Value(VCon), Values)

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
iWilds (α : αs) = IWild :>> iWilds αs

iOrInv :: Instance -> Either Instance Instance
iOrInv (IOrL h) = Left h
iOrInv (IOrR h) = Right h

iConInv :: Instance -> Instances
iConInv (ICon c is) = is

iUncons :: Instances -> (Instance, Instances)
iUncons (i :>> is) = (i, is)

infix 4 `decInstance`
decInstance :: Pattern -> Value -> DecP Instance
decInstance PWild v = Yes IWild
decInstance (POr p q) v
  = mapDecP (either IOrL IOrR)
      (eitherDecP (decInstance p v) (decInstance q v))
decInstance (PCon c ps) (VCon c' vs)
  = if c == c' then mapDecP (\ is -> ICon c is) (decInstances ps vs)
      else No

infix 4 `decInstances`
decInstances :: Patterns -> Values -> DecP Instances
decInstances Nil Nil = Yes HNil
decInstances (p :> ps) (v :> vs)
  = mapDecP (uncurry (:>>))
      (tupleDecP (decInstance p v) (decInstances ps vs))

type Match = First Instances

decMatch :: [Patterns] -> Values -> DecP Match
decMatch p vs = firstDecP (\ ps -> decInstances ps vs) p

