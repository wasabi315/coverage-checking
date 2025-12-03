module CoverageCheck.Usefulness.Algorithm.Raw where

import CoverageCheck.Name (Name, anyNameIn', nameInSet')
import CoverageCheck.Prelude (All(Nil, (:>)), headAll, tailAll)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, pWilds)
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
rootConSet = foldMap (rootConSet' . headAll . headAll)

default' :: All Patterns -> [All Patterns]
default' ((PWild :> ps) :> pss) = [ps :> pss]
default' ((PCon c rs :> ps) :> pss) = []
default' ((POr r₁ r₂ :> ps) :> pss)
  = default' ((r₁ :> ps) :> pss) ++ default' ((r₂ :> ps) :> pss)

default_ :: [All Patterns] -> [All Patterns]
default_ = concatMap default'

existMissCon :: Signature -> Name -> [All Patterns] -> Bool
existMissCon sig d psmat = not (Data.Set.null missConSet)
  where
    conSet :: Set Name
    conSet = rootConSet psmat
    missConSet :: Set Name
    missConSet
      = Data.Set.difference (nameInSet' (dataCons (dataDefs sig d)))
          conSet

isUseful ::
         Signature -> [Tys] -> [All Patterns] -> All Patterns -> Bool
isUseful sig [] [] Nil = True
isUseful sig [] (_ : _) Nil = False
isUseful sig ([] : αss) psmat (_ :> pss)
  = isUseful sig αss (map tailAll psmat) pss
isUseful sig ((TyData d : αs) : αss) psmat ((PWild :> ps) :> pss)
  = if existMissCon sig d psmat then
      isUseful sig (αs : αss) (default_ psmat) (ps :> pss) else
      anyNameIn' (dataCons (dataDefs sig d))
        (\ x ->
           isUseful sig (argsTy (dataDefs sig d) x : (αs : αss))
             (specialize sig d x psmat)
             (pWilds (argsTy (dataDefs sig d) x) :> (ps :> pss)))
isUseful sig ((TyData d : αs) : αss) psmat
  ((PCon c rs :> ps) :> pss)
  = isUseful sig (argsTy (dataDefs sig d) c : (αs : αss))
      (specialize sig d c psmat)
      (rs :> (ps :> pss))
isUseful sig ((TyData d : αs) : αss) psmat
  ((POr r₁ r₂ :> ps) :> pss)
  = isUseful sig ((TyData d : αs) : αss) psmat ((r₁ :> ps) :> pss) ||
      isUseful sig ((TyData d : αs) : αss) psmat ((r₂ :> ps) :> pss)

