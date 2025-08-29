{-# LANGUAGE ScopedTypeVariables #-}
module CoverageCheck.Usefulness.Algorithm where

import CoverageCheck.Name (Name, anyNameIn', decPAnyNameIn)
import CoverageCheck.Prelude (All(Nil, (:>)), DecP(No, Yes), NonEmpty(MkNonEmpty), These, headAll, mapDecP, tailAll, theseDecP)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, Value, headPattern, pWilds)
import Data.Set (Set)
import qualified Data.Set (difference, empty, fromList, null, singleton, toAscList, union)

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
      = Data.Set.difference
          (Data.Set.fromList (dataCons (dataDefs sig d)))
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

decExistMissCon ::
                Signature ->
                  Name -> [All Patterns] -> Either () (Either () (NonEmpty Name))
decExistMissCon sig d psss
  = case
      case Data.Set.toAscList missConSet of
          [] -> Left ()
          x : xs -> Right (MkNonEmpty x xs)
      of
        Left () -> Left ()
        Right misses -> Right
                          (if Data.Set.null conSet then Left () else Right misses)
  where
    conSet :: Set Name
    conSet = rootConSet psss
    missConSet :: Set Name
    missConSet
      = Data.Set.difference
          (Data.Set.fromList (dataCons (dataDefs sig d)))
          conSet

class Usefulness u where
    nilOkCase :: Signature -> (Ty -> Value) -> u
    tailCase :: Signature -> (Ty -> Value) -> u -> u
    orCase :: Signature -> (Ty -> Value) -> These u u -> u
    conCase :: Signature -> (Ty -> Value) -> Name -> Name -> u -> u
    wildMissCase ::
                 Signature ->
                   (Ty -> Value) -> Name -> Either () (NonEmpty Name) -> u -> u
    wildCompCase ::
                 Signature -> (Ty -> Value) -> Name -> NonEmpty (Name, u) -> u

decUseful' ::
           forall u . Usefulness u =>
             Signature ->
               (Ty -> Value) -> [Tys] -> [All Patterns] -> All Patterns -> DecP u
decUseful' sig nonEmptyAxiom [] [] Nil
  = Yes (nilOkCase sig nonEmptyAxiom)
decUseful' sig nonEmptyAxiom [] (_ : _) Nil = No
decUseful' sig nonEmptyAxiom ([] : αss) psss (Nil :> pss)
  = mapDecP (tailCase sig nonEmptyAxiom)
      (decUseful' sig nonEmptyAxiom αss (map tailAll psss) pss)
decUseful' sig nonEmptyAxiom ((TyData d : αs) : αss) psss
  ((PWild :> ps) :> pss)
  = case decExistMissCon sig d psss of
        Right miss -> mapDecP (wildMissCase sig nonEmptyAxiom d miss)
                        (decUseful' sig nonEmptyAxiom (αs : αss) (default_ psss)
                           (ps :> pss))
        Left () -> mapDecP (wildCompCase sig nonEmptyAxiom d)
                     (decPAnyNameIn (dataCons (dataDefs sig d))
                        (\ c ->
                           decUseful' sig nonEmptyAxiom
                             (argsTy (dataDefs sig d) c : (αs : αss))
                             (specialize sig d c psss)
                             (pWilds (argsTy (dataDefs sig d) c) :> (ps :> pss))))
decUseful' sig nonEmptyAxiom ((TyData d : αs) : αss) psss
  ((PCon c rs :> ps) :> pss)
  = mapDecP (conCase sig nonEmptyAxiom d c)
      (decUseful' sig nonEmptyAxiom
         (argsTy (dataDefs sig d) c : (αs : αss))
         (specialize sig d c psss)
         (rs :> (ps :> pss)))
decUseful' sig nonEmptyAxiom ((TyData d : αs) : αss) psss
  ((POr r₁ r₂ :> ps) :> pss)
  = mapDecP (orCase sig nonEmptyAxiom)
      (theseDecP
         (decUseful' sig nonEmptyAxiom ((TyData d : αs) : αss) psss
            ((r₁ :> ps) :> pss))
         (decUseful' sig nonEmptyAxiom ((TyData d : αs) : αss) psss
            ((r₂ :> ps) :> pss)))

decUseful ::
          forall u . Usefulness u =>
            Signature ->
              (Ty -> Value) -> Tys -> [Patterns] -> Patterns -> DecP u
decUseful sig nonEmptyAxiom αs pss ps
  = decUseful' sig nonEmptyAxiom [αs] (map (:> Nil) pss) (ps :> Nil)

