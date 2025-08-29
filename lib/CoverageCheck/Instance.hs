module CoverageCheck.Instance where

import Control.Arrow (first)
import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Cons, Nil), Any, DecP(No, Yes), First, eitherDecP, firstDecP, mapDecP, tupleDecP)
import CoverageCheck.Syntax (Pattern(PCon, POr, PWild), Patterns, Tys, Value(VCon), Values, pWilds)

data Instance = IWild
              | ICon Name Instances
              | IOrL Instance
              | IOrR Instance
                  deriving Show

data Instances = INil
               | ICons Instance Instances
                   deriving Show

infix 4 `InstanceMatrix`
type InstanceMatrix = Any Instances

iWilds :: Tys -> Instances
iWilds [] = INil
iWilds (α : αs) = ICons IWild (iWilds αs)

iOrInv :: Instance -> Either Instance Instance
iOrInv (IOrL h) = Left h
iOrInv (IOrR h) = Right h

iConInv :: Instance -> Instances
iConInv (ICon c is) = is

iUncons :: Instances -> (Instance, Instances)
iUncons (ICons i is) = (i, is)

infixr 5 `appendInstances`
appendInstances :: Instances -> Instances -> Instances
appendInstances INil is2 = is2
appendInstances (ICons i1 is1) is2
  = ICons i1 (appendInstances is1 is2)

unappendInstances ::
                  Patterns -> Instances -> (Instances, Instances)
unappendInstances Nil is = (INil, is)
unappendInstances (Cons p ps) (ICons i is)
  = first (ICons i) (unappendInstances ps is)

splitInstances :: Tys -> Values -> (Values, Values)
splitInstances [] us = (Nil, us)
splitInstances (α : αs) (Cons u us)
  = first (Cons u) (splitInstances αs us)

wildHeadLemma :: Tys -> Instances -> Instances
wildHeadLemma βs h
  = case unappendInstances (pWilds βs) h of
        (_, h') -> ICons IWild h'

wildHeadLemmaInv :: Tys -> Instances -> Instances
wildHeadLemmaInv βs (ICons IWild h) = appendInstances (iWilds βs) h

orHeadLemma :: Either Instances Instances -> Instances
orHeadLemma (Left (ICons h hs)) = ICons (IOrL h) hs
orHeadLemma (Right (ICons h hs)) = ICons (IOrR h) hs

orHeadLemmaInv :: Instances -> Either Instances Instances
orHeadLemmaInv (ICons (IOrL h) hs) = Left (ICons h hs)
orHeadLemmaInv (ICons (IOrR h) hs) = Right (ICons h hs)

conHeadLemma :: Name -> Patterns -> Instances -> Instances
conHeadLemma c rs h
  = case unappendInstances rs h of
        (h1, h2) -> ICons (ICon c h1) h2

conHeadLemmaInv :: Patterns -> Instances -> Instances
conHeadLemmaInv rs (ICons (ICon c h) h') = appendInstances h h'

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
decInstances Nil Nil = Yes INil
decInstances (Cons p ps) (Cons v vs)
  = mapDecP (uncurry ICons)
      (tupleDecP (decInstance p v) (decInstances ps vs))

type Match = First Instances

decMatch :: [Patterns] -> Values -> DecP Match
decMatch p vs = firstDecP (\ ps -> decInstances ps vs) p

