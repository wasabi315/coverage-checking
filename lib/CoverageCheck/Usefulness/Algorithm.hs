{-# LANGUAGE ScopedTypeVariables #-}
module CoverageCheck.Usefulness.Algorithm where

import CoverageCheck.Name (Name, anyNameIn', decPAnyNameIn)
import CoverageCheck.Prelude (All(Cons, Nil), DecP(No, Yes), NonEmpty(MkNonEmpty), These, appendAll, mapDecP, theseDecP)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, Value, headPattern, pWilds)
import Data.Set (Set)
import qualified Data.Set (difference, empty, fromList, null, singleton, toAscList, union)

specialize' :: Signature -> Name -> Name -> Patterns -> [Patterns]
specialize' sig d c (Cons PWild ps)
  = [appendAll (pWilds (argsTy (dataDefs sig d) c)) ps]
specialize' sig d c (Cons (PCon c' rs) ps)
  = if c == c' then [appendAll rs ps] else []
specialize' sig d c (Cons (POr r₁ r₂) ps)
  = specialize' sig d c (Cons r₁ ps) ++
      specialize' sig d c (Cons r₂ ps)

specialize :: Signature -> Name -> Name -> [Patterns] -> [Patterns]
specialize sig d c = concatMap (specialize' sig d c)

rootConSet' :: Pattern -> Set Name
rootConSet' PWild = Data.Set.empty
rootConSet' (PCon c _) = Data.Set.singleton c
rootConSet' (POr p q)
  = Data.Set.union (rootConSet' p) (rootConSet' q)

rootConSet :: [Patterns] -> Set Name
rootConSet pss
  = foldr (\ ps -> Data.Set.union (rootConSet' (headPattern ps)))
      Data.Set.empty
      pss

default' :: Patterns -> [Patterns]
default' (Cons PWild ps) = [ps]
default' (Cons (PCon _ _) ps) = []
default' (Cons (POr r₁ r₂) ps)
  = default' (Cons r₁ ps) ++ default' (Cons r₂ ps)

default_ :: [Patterns] -> [Patterns]
default_ = concatMap default'

existMissCon :: Signature -> Name -> [Patterns] -> Bool
existMissCon sig d pss = not (Data.Set.null missConSet)
  where
    conSet :: Set Name
    conSet = rootConSet pss
    missConSet :: Set Name
    missConSet
      = Data.Set.difference
          (Data.Set.fromList (dataCons (dataDefs sig d)))
          conSet

isUseful :: Signature -> Tys -> [Patterns] -> Patterns -> Bool
isUseful sig [] [] Nil = True
isUseful sig [] (_ : _) Nil = False
isUseful sig (TyData d : αs) pss (Cons PWild ps)
  = if existMissCon sig d pss then isUseful sig αs (default_ pss) ps
      else
      anyNameIn'
        (\ x ->
           isUseful sig (argsTy (dataDefs sig d) x ++ αs)
             (specialize sig d x pss)
             (appendAll (pWilds (argsTy (dataDefs sig d) x)) ps))
        (dataCons (dataDefs sig d))
isUseful sig (TyData d : αs) pss (Cons (PCon c rs) ps)
  = isUseful sig (argsTy (dataDefs sig d) c ++ αs)
      (specialize sig d c pss)
      (appendAll rs ps)
isUseful sig (TyData d : αs) pss (Cons (POr r₁ r₂) ps)
  = isUseful sig (TyData d : αs) pss (Cons r₁ ps) ||
      isUseful sig (TyData d : αs) pss (Cons r₂ ps)

decExistMissCon ::
                Signature ->
                  Name -> [Patterns] -> Either () (Either () (NonEmpty Name))
decExistMissCon sig d pss
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
    conSet = rootConSet pss
    missConSet :: Set Name
    missConSet
      = Data.Set.difference
          (Data.Set.fromList (dataCons (dataDefs sig d)))
          conSet

class Usefulness u where
    nilOkCase :: Signature -> (Ty -> Value) -> u
    orCase :: Signature -> (Ty -> Value) -> These u u -> u
    conCase :: Signature -> (Ty -> Value) -> Name -> Name -> u -> u
    wildMissCase ::
                 Signature ->
                   (Ty -> Value) -> Name -> Either () (NonEmpty Name) -> u -> u
    wildCompCase ::
                 Signature -> (Ty -> Value) -> Name -> NonEmpty (Name, u) -> u

decUseful ::
          forall u . Usefulness u =>
            Signature ->
              (Ty -> Value) -> Tys -> [Patterns] -> Patterns -> DecP u
decUseful sig nonEmptyAxiom [] [] Nil
  = Yes (nilOkCase sig nonEmptyAxiom)
decUseful sig nonEmptyAxiom [] (_ : _) Nil = No
decUseful sig nonEmptyAxiom (TyData d : αs) pss (Cons PWild ps)
  = case decExistMissCon sig d pss of
        Right miss -> mapDecP (wildMissCase sig nonEmptyAxiom d miss)
                        (decUseful sig nonEmptyAxiom αs (default_ pss) ps)
        Left () -> mapDecP (wildCompCase sig nonEmptyAxiom d)
                     (decPAnyNameIn (dataCons (dataDefs sig d))
                        (\ c ->
                           decUseful sig nonEmptyAxiom (argsTy (dataDefs sig d) c ++ αs)
                             (specialize sig d c pss)
                             (appendAll (pWilds (argsTy (dataDefs sig d) c)) ps)))
decUseful sig nonEmptyAxiom (TyData d : αs) pss
  (Cons (PCon c rs) ps)
  = mapDecP (conCase sig nonEmptyAxiom d c)
      (decUseful sig nonEmptyAxiom (argsTy (dataDefs sig d) c ++ αs)
         (specialize sig d c pss)
         (appendAll rs ps))
decUseful sig nonEmptyAxiom (TyData d : αs) pss
  (Cons (POr r₁ r₂) ps)
  = mapDecP (orCase sig nonEmptyAxiom)
      (theseDecP
         (decUseful sig nonEmptyAxiom (TyData d : αs) pss (Cons r₁ ps))
         (decUseful sig nonEmptyAxiom (TyData d : αs) pss (Cons r₂ ps)))

