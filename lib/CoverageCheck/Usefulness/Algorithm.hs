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

usefulNilOkCase :: NonEmpty (All Patterns)
usefulNilOkCase = Nil :| []

usefulTailCase' :: All Patterns -> All Patterns
usefulTailCase' qss = Nil :> qss

usefulOrCase ::
             These (NonEmpty (All Patterns)) (NonEmpty (All Patterns)) ->
               NonEmpty (All Patterns)
usefulOrCase (This hs) = hs
usefulOrCase (That hs) = hs
usefulOrCase (Both hs1 hs2) = hs1 <> hs2

usefulConCase' :: Name -> All Patterns -> All Patterns
usefulConCase' c (qs' :> (qs :> qss)) = (PCon c qs' :> qs) :> qss

usefulWildCompCase' :: Name -> All Patterns -> All Patterns
usefulWildCompCase' c (qs' :> (qs :> qss))
  = (PCon c qs' :> qs) :> qss

usefulWildCompCase ::
                   NonEmpty (Name, NonEmpty (All Patterns)) -> NonEmpty (All Patterns)
usefulWildCompCase hs
  = do (c, hs') <- hs
       fmap (usefulWildCompCase' c) hs'

usefulWildMissCase' ::
                    Signature ->
                      Name ->
                        Either () (NonEmpty Name) ->
                          All Patterns -> NonEmpty (All Patterns)
usefulWildMissCase' sig d (Left ()) (qs :> qss)
  = ((PWild :> qs) :> qss) :| []
usefulWildMissCase' sig d (Right hs) (qs :> qss)
  = fmap
      (\ c -> (PCon c (pWilds (argsTy (dataDefs sig d) c)) :> qs) :> qss)
      hs

usefulWildMissCase ::
                   Signature ->
                     Name ->
                       Either () (NonEmpty Name) ->
                         NonEmpty (All Patterns) -> NonEmpty (All Patterns)
usefulWildMissCase sig d h hs = hs >>= usefulWildMissCase' sig d h

decUseful' ::
           Signature ->
             [Tys] ->
               [All Patterns] -> All Patterns -> DecP (NonEmpty (All Patterns))
decUseful' sig [] [] Nil = Yes usefulNilOkCase
decUseful' sig [] (_ : _) Nil = No
decUseful' sig ([] : αss) psss (Nil :> pss)
  = mapDecP (fmap usefulTailCase')
      (decUseful' sig αss (map tailAll psss) pss)
decUseful' sig ((TyData d : αs) : αss) psss ((PWild :> ps) :> pss)
  = case decExistMissCon sig d psss of
        Right miss -> mapDecP (usefulWildMissCase sig d miss)
                        (decUseful' sig (αs : αss) (default_ psss) (ps :> pss))
        Left () -> mapDecP usefulWildCompCase
                     (decPAnyNameIn (dataCons (dataDefs sig d))
                        (\ c ->
                           decUseful' sig (argsTy (dataDefs sig d) c : (αs : αss))
                             (specialize sig d c psss)
                             (pWilds (argsTy (dataDefs sig d) c) :> (ps :> pss))))
decUseful' sig ((TyData d : αs) : αss) psss
  ((PCon c rs :> ps) :> pss)
  = mapDecP (fmap (usefulConCase' c))
      (decUseful' sig (argsTy (dataDefs sig d) c : (αs : αss))
         (specialize sig d c psss)
         (rs :> (ps :> pss)))
decUseful' sig ((TyData d : αs) : αss) psss
  ((POr r₁ r₂ :> ps) :> pss)
  = mapDecP usefulOrCase
      (theseDecP
         (decUseful' sig ((TyData d : αs) : αss) psss ((r₁ :> ps) :> pss))
         (decUseful' sig ((TyData d : αs) : αss) psss ((r₂ :> ps) :> pss)))

decUseful ::
          Signature -> Tys -> [Patterns] -> Patterns -> DecP Useful
decUseful sig αs pss ps
  = mapDecP
      (\ h ->
         Useful
           (fmap
              (\case
                   qs :> Nil -> qs)
              h))
      (decUseful' sig [αs] (map (:> Nil) pss) (ps :> Nil))

