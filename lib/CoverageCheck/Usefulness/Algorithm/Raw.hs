module CoverageCheck.Usefulness.Algorithm.Raw where

import CoverageCheck.Name (Name, allNameInSet', anyNameIn')
import CoverageCheck.Prelude (All(Nil, (:>)), headAll, tailAll)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, headPattern, pWilds)
import Data.Set (Set)
import qualified Data.Set (difference, empty, null, singleton, union)

specialize' ::
            Signature -> Name -> Name -> All Patterns -> [All Patterns]
specialize' sig d c ((PWild :> ps) :> pss)
  = [pWilds (argsTy (dataDefs sig d) c) :> (ps :> pss)]
specialize' sig d c ((PCon c' rs :> ps) :> pss)
  = if c == c' then [rs :> (ps :> pss)] else []
specialize' sig d c ((POr r₁ r₂ :> ps) :> pss)
  = specialize' sig d c ((r₁ :> ps) :> pss) ++
      specialize' sig d c ((r₂ :> ps) :> pss)

specialize ::
           Signature -> Name -> Name -> [All Patterns] -> [All Patterns]
specialize sig d c = concatMap (specialize' sig d c)

rootConSet' :: Pattern -> Set Name
rootConSet' PWild = Data.Set.empty
rootConSet' (PCon c _) = Data.Set.singleton c
rootConSet' (POr p q)
  = Data.Set.union (rootConSet' p) (rootConSet' q)

rootConSet :: [All Patterns] -> Set Name
rootConSet psss
  = foldr
      (\ pss -> Data.Set.union (rootConSet' (headPattern (headAll pss))))
      Data.Set.empty
      psss

default' :: All Patterns -> [All Patterns]
default' ((PWild :> ps) :> pss) = [ps :> pss]
default' ((PCon c rs :> ps) :> pss) = []
default' ((POr r₁ r₂ :> ps) :> pss)
  = default' ((r₁ :> ps) :> pss) ++ default' ((r₂ :> ps) :> pss)

default_ :: [All Patterns] -> [All Patterns]
default_ = concatMap default'

existMissCon :: Signature -> Name -> [All Patterns] -> Bool
existMissCon sig d psss = not (Data.Set.null missConSet)
  where
    conSet :: Set Name
    conSet = rootConSet psss
    missConSet :: Set Name
    missConSet
      = Data.Set.difference (allNameInSet' (dataCons (dataDefs sig d)))
          conSet

isUseful ::
         Signature -> [Tys] -> [All Patterns] -> All Patterns -> Bool
isUseful sig [] [] Nil = True
isUseful sig [] (_ : _) Nil = False
isUseful sig ([] : αss) psss (_ :> pss)
  = isUseful sig αss (map tailAll psss) pss
isUseful sig ((TyData d : αs) : αss) psss ((PWild :> ps) :> pss)
  = if existMissCon sig d psss then
      isUseful sig (αs : αss) (default_ psss) (ps :> pss) else
      anyNameIn'
        (\ x ->
           isUseful sig (argsTy (dataDefs sig d) x : (αs : αss))
             (specialize sig d x psss)
             (pWilds (argsTy (dataDefs sig d) x) :> (ps :> pss)))
        (dataCons (dataDefs sig d))
isUseful sig ((TyData d : αs) : αss) psss
  ((PCon c rs :> ps) :> pss)
  = isUseful sig (argsTy (dataDefs sig d) c : (αs : αss))
      (specialize sig d c psss)
      (rs :> (ps :> pss))
isUseful sig ((TyData d : αs) : αss) psss
  ((POr r₁ r₂ :> ps) :> pss)
  = isUseful sig ((TyData d : αs) : αss) psss ((r₁ :> ps) :> pss) ||
      isUseful sig ((TyData d : αs) : αss) psss ((r₂ :> ps) :> pss)

