module CoverageCheck.Usefulness.Algorithm where

import CoverageCheck.Name (Name, decPAnyNameIn)
import CoverageCheck.Prelude (All(Nil, (:>)), DecP(No, Yes), These(Both, That, This), mapDecP, tailAll, theseDecP)
import CoverageCheck.Syntax (Dataty(argsTy, dataCons), Pattern(PCon, POr, PWild), Patterns, Signature(dataDefs), Ty(TyData), Tys, pWilds)
import CoverageCheck.Usefulness.Algorithm.MissingConstructors (decExistMissCon)
import CoverageCheck.Usefulness.Algorithm.Raw (default_, specialize)
import CoverageCheck.Usefulness.Definition (Useful(MkUseful))
import Data.List.NonEmpty (NonEmpty((:|)))

usefulNilOkCase :: Useful
usefulNilOkCase = MkUseful (Nil :| [])

usefulTailCase' :: All Patterns -> All Patterns
usefulTailCase' qss = Nil :> qss

usefulTailCase :: Useful -> Useful
usefulTailCase (MkUseful hs) = MkUseful (fmap usefulTailCase' hs)

usefulOrCase :: These Useful Useful -> Useful
usefulOrCase (This (MkUseful hs)) = MkUseful hs
usefulOrCase (That (MkUseful hs)) = MkUseful hs
usefulOrCase (Both (MkUseful hs) (MkUseful hs'))
  = MkUseful (hs <> hs')

usefulConCase' :: Name -> All Patterns -> All Patterns
usefulConCase' c (qs' :> (qs :> qss)) = (PCon c qs' :> qs) :> qss

usefulConCase :: Name -> Useful -> Useful
usefulConCase c (MkUseful hs)
  = MkUseful (fmap (usefulConCase' c) hs)

usefulWildCompCase' :: Name -> All Patterns -> All Patterns
usefulWildCompCase' c (qs' :> (qs :> qss))
  = (PCon c qs' :> qs) :> qss

usefulWildCompCase :: NonEmpty (Name, Useful) -> Useful
usefulWildCompCase hs
  = MkUseful
      (do (c, MkUseful hs') <- hs
          fmap (usefulWildCompCase' c) hs')

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
                   Signature -> Name -> Either () (NonEmpty Name) -> Useful -> Useful
usefulWildMissCase sig d h (MkUseful hs)
  = MkUseful (hs >>= usefulWildMissCase' sig d h)

decUseful' ::
           Signature -> [Tys] -> [All Patterns] -> All Patterns -> DecP Useful
decUseful' sig [] [] Nil = Yes usefulNilOkCase
decUseful' sig [] (_ : _) Nil = No
decUseful' sig ([] : αss) psss (Nil :> pss)
  = mapDecP usefulTailCase
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
  = mapDecP (usefulConCase c)
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
  = decUseful' sig [αs] (map (:> Nil) pss) (ps :> Nil)

