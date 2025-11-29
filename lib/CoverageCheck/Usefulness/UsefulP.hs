module CoverageCheck.Usefulness.UsefulP where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Nil, (:>)), These(Both, That, This))
import CoverageCheck.Syntax (Dataty(argsTy), Pattern(PCon, PWild), Patterns, Signature(dataDefs), pWilds)
import CoverageCheck.Usefulness.Algorithm (Usefulness)
import Data.List.NonEmpty (NonEmpty((:|)))

import CoverageCheck.Usefulness.Algorithm

newtype UsefulP = MkUsefulP{witnesses :: NonEmpty (All Patterns)}

usefulPNilOkCase :: UsefulP
usefulPNilOkCase = MkUsefulP (Nil :| [])

usefulPTailCase' :: All Patterns -> All Patterns
usefulPTailCase' qss = Nil :> qss

usefulPTailCase :: UsefulP -> UsefulP
usefulPTailCase (MkUsefulP hs)
  = MkUsefulP (fmap usefulPTailCase' hs)

usefulPOrCase :: These UsefulP UsefulP -> UsefulP
usefulPOrCase (This (MkUsefulP hs)) = MkUsefulP hs
usefulPOrCase (That (MkUsefulP hs)) = MkUsefulP hs
usefulPOrCase (Both (MkUsefulP hs) (MkUsefulP hs'))
  = MkUsefulP (hs <> hs')

usefulPConCase' :: Name -> All Patterns -> All Patterns
usefulPConCase' c (qs' :> (qs :> qss)) = (PCon c qs' :> qs) :> qss

usefulPConCase :: Name -> UsefulP -> UsefulP
usefulPConCase c (MkUsefulP hs)
  = MkUsefulP (fmap (usefulPConCase' c) hs)

usefulPWildCompCase' :: Name -> All Patterns -> All Patterns
usefulPWildCompCase' c (qs' :> (qs :> qss))
  = (PCon c qs' :> qs) :> qss

usefulPWildCompCase :: NonEmpty (Name, UsefulP) -> UsefulP
usefulPWildCompCase hs
  = MkUsefulP
      (do (c, MkUsefulP hs') <- hs
          fmap (usefulPWildCompCase' c) hs')

usefulPWildMissCase' ::
                     Signature ->
                       Name ->
                         Either () (NonEmpty Name) ->
                           All Patterns -> NonEmpty (All Patterns)
usefulPWildMissCase' sig d (Left ()) (qs :> qss)
  = ((PWild :> qs) :> qss) :| []
usefulPWildMissCase' sig d (Right hs) (qs :> qss)
  = fmap
      (\ c -> (PCon c (pWilds (argsTy (dataDefs sig d) c)) :> qs) :> qss)
      hs

usefulPWildMissCase ::
                    Signature ->
                      Name -> Either () (NonEmpty Name) -> UsefulP -> UsefulP
usefulPWildMissCase sig d h (MkUsefulP hs)
  = MkUsefulP (hs >>= usefulPWildMissCase' sig d h)

instance Usefulness UsefulP where
    nilOkCase sig nonEmptyAxiom = usefulPNilOkCase
    tailCase sig nonEmptyAxiom = usefulPTailCase
    orCase sig nonEmptyAxiom = usefulPOrCase
    conCase sig nonEmptyAxiom d c = usefulPConCase c
    wildMissCase sig nonEmptyAxiom d = usefulPWildMissCase sig d
    wildCompCase sig nonEmptyAxiom d = usefulPWildCompCase

