module CoverageCheck.Instance where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Nil, (:>)), Any, DecP(No, Yes), First, HPointwise(HNil, (:>>)), eitherDecP, firstDecP, mapDecP, tupleDecP)
import CoverageCheck.Syntax (Pattern(PCon, POr, PWild), Patterns, Tys, Value(VCon), Values)

data Instance = IWild
              | ICon Name Instances
              | IOrL Instance
              | IOrR Instance
                  deriving Show

infix 4 `Instances`
type Instances = HPointwise Instance

infix 4 `InstanceMatrix`
type InstanceMatrix = Any Instances

iWilds :: Tys -> Instances
iWilds [] = HNil
iWilds (α : αs) = IWild :>> iWilds αs

iOrInv :: Instance -> Either Instance Instance
iOrInv (IOrL inst) = Left inst
iOrInv (IOrR inst) = Right inst

iConInv :: Instance -> Instances
iConInv (ICon c insts) = insts

iUncons :: Instances -> (Instance, Instances)
iUncons (inst :>> insts) = (inst, insts)

infix 4 `decInstance`
decInstance :: Pattern -> Value -> DecP Instance
decInstance PWild v = Yes IWild
decInstance (POr p q) v
  = mapDecP (either IOrL IOrR)
      (eitherDecP (decInstance p v) (decInstance q v))
decInstance (PCon c ps) (VCon c' vs)
  = if c == c' then
      mapDecP (\ insts -> ICon c insts) (decInstances ps vs) else No

infix 4 `decInstances`
decInstances :: Patterns -> Values -> DecP Instances
decInstances Nil Nil = Yes HNil
decInstances (p :> ps) (v :> vs)
  = mapDecP (uncurry (:>>))
      (tupleDecP (decInstance p v) (decInstances ps vs))

type FirstMatch = First Instances

decPFirstMatch :: [Patterns] -> Values -> DecP FirstMatch
decPFirstMatch pmat vs
  = firstDecP (\ ps -> decInstances ps vs) pmat

