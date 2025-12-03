{-# LANGUAGE LambdaCase #-}
module CoverageCheck.Usefulness.Algorithm where

import CoverageCheck.Name (Name, decPAnyNameIn)
import CoverageCheck.Prelude (All(Nil, (:>)), DecP(No, Yes), These(Both, That, This), mapDecP, tailAll, theseDecP)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, pWilds)
import CoverageCheck.Usefulness.Algorithm.MissingConstructors (decExistMissCon)
import CoverageCheck.Usefulness.Algorithm.Raw (default_, specialize)
import CoverageCheck.Usefulness.Definition (Useful)
import Data.List.NonEmpty (NonEmpty((:|)))

import CoverageCheck.Usefulness.Definition (Useful(..))

nilOkCase :: NonEmpty (All Patterns)
nilOkCase = Nil :| []

tailCase' :: All Patterns -> All Patterns
tailCase' qss = Nil :> qss

orCase ::
       These (NonEmpty (All Patterns)) (NonEmpty (All Patterns)) ->
         NonEmpty (All Patterns)
orCase (This hs) = hs
orCase (That hs) = hs
orCase (Both hs1 hs2) = hs1 <> hs2

conCase' :: Name -> All Patterns -> All Patterns
conCase' c (qs' :> (qs :> qss)) = (PCon c qs' :> qs) :> qss

wildCompCase' :: Name -> All Patterns -> All Patterns
wildCompCase' c (qs' :> (qs :> qss)) = (PCon c qs' :> qs) :> qss

wildCompCase ::
             NonEmpty (Name, NonEmpty (All Patterns)) -> NonEmpty (All Patterns)
wildCompCase hs
  = do (c, hs') <- hs
       fmap (wildCompCase' c) hs'

wildMissCase' ::
              Signature ->
                Name ->
                  Either () (NonEmpty Name) ->
                    All Patterns -> NonEmpty (All Patterns)
wildMissCase' sig d (Left ()) (qs :> qss)
  = ((PWild :> qs) :> qss) :| []
wildMissCase' sig d (Right hs) (qs :> qss)
  = fmap
      (\ c -> (PCon c (pWilds (argsTy (dataDefs sig d) c)) :> qs) :> qss)
      hs

wildMissCase ::
             Signature ->
               Name ->
                 Either () (NonEmpty Name) ->
                   NonEmpty (All Patterns) -> NonEmpty (All Patterns)
wildMissCase sig d h hs = hs >>= wildMissCase' sig d h

decUseful' ::
           Signature ->
             [Tys] ->
               [All Patterns] -> All Patterns -> DecP (NonEmpty (All Patterns))
decUseful' sig [] [] Nil = Yes nilOkCase
decUseful' sig [] (_ : _) Nil = No
decUseful' sig ([] : αss) psmat (Nil :> pss)
  = mapDecP (fmap tailCase')
      (decUseful' sig αss (map tailAll psmat) pss)
decUseful' sig ((TyData d : αs) : αss) psmat ((PWild :> ps) :> pss)
  = case decExistMissCon sig d psmat of
        Right miss -> mapDecP (wildMissCase sig d miss)
                        (decUseful' sig (αs : αss) (default_ psmat) (ps :> pss))
        Left () -> mapDecP wildCompCase
                     (decPAnyNameIn (dataCons (dataDefs sig d))
                        (\ c ->
                           decUseful' sig (argsTy (dataDefs sig d) c : (αs : αss))
                             (specialize sig d c psmat)
                             (pWilds (argsTy (dataDefs sig d) c) :> (ps :> pss))))
decUseful' sig ((TyData d : αs) : αss) psmat
  ((PCon c rs :> ps) :> pss)
  = mapDecP (fmap (conCase' c))
      (decUseful' sig (argsTy (dataDefs sig d) c : (αs : αss))
         (specialize sig d c psmat)
         (rs :> (ps :> pss)))
decUseful' sig ((TyData d : αs) : αss) psmat
  ((POr r₁ r₂ :> ps) :> pss)
  = mapDecP orCase
      (theseDecP
         (decUseful' sig ((TyData d : αs) : αss) psmat ((r₁ :> ps) :> pss))
         (decUseful' sig ((TyData d : αs) : αss) psmat ((r₂ :> ps) :> pss)))

decUseful ::
          Signature -> Tys -> [Patterns] -> Patterns -> DecP Useful
decUseful sig αs pmat ps
  = mapDecP
      (\ h ->
         Useful
           (fmap
              (\case
                   qs :> Nil -> qs)
              h))
      (decUseful' sig [αs] (map (:> Nil) pmat) (ps :> Nil))

