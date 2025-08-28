module CoverageCheck.Usefulness.UsefulP where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (NonEmpty(MkNonEmpty), These(Both, That, This))
import CoverageCheck.Subsumption (splitSubsumptions)
import CoverageCheck.Syntax (Dataty(argsTy), Pattern(PCon, PWild), Patterns(PCons, PNil), Signature(dataDefs), pWilds)
import CoverageCheck.Usefulness.Algorithm (Usefulness)

import CoverageCheck.Usefulness.Algorithm

newtype UsefulP = MkUsefulP{witnesses :: NonEmpty Patterns}

usefulPNilOkCase :: UsefulP
usefulPNilOkCase = MkUsefulP (MkNonEmpty PNil [])

usefulPOrCase :: These UsefulP UsefulP -> UsefulP
usefulPOrCase (This (MkUsefulP hs)) = MkUsefulP hs
usefulPOrCase (That (MkUsefulP hs)) = MkUsefulP hs
usefulPOrCase (Both (MkUsefulP hs) (MkUsefulP hs'))
  = MkUsefulP (hs <> hs')

usefulPConCase' ::
                Signature -> Name -> Name -> Patterns -> Patterns
usefulPConCase' sig d c qs
  = case splitSubsumptions (argsTy (dataDefs sig d) c) qs of
        (qs₁, qs₂) -> PCons (PCon c qs₁) qs₂

usefulPConCase :: Signature -> Name -> Name -> UsefulP -> UsefulP
usefulPConCase sig d c (MkUsefulP hs)
  = MkUsefulP (fmap (usefulPConCase' sig d c) hs)

usefulPWildCompCase' ::
                     Signature -> Name -> Name -> Patterns -> Patterns
usefulPWildCompCase' sig d c qs
  = case splitSubsumptions (argsTy (dataDefs sig d) c) qs of
        (qs₁, qs₂) -> PCons (PCon c qs₁) qs₂

usefulPWildCompCase ::
                    Signature -> Name -> NonEmpty (Name, UsefulP) -> UsefulP
usefulPWildCompCase sig d hs
  = MkUsefulP
      (do (c, MkUsefulP hs') <- hs
          fmap (usefulPWildCompCase' sig d c) hs')

usefulPWildMissCase' ::
                     Signature ->
                       Name -> Either () (NonEmpty Name) -> Patterns -> NonEmpty Patterns
usefulPWildMissCase' sig d (Left ()) qs
  = MkNonEmpty (PCons PWild qs) []
usefulPWildMissCase' sig d (Right hs) qs
  = flip fmap hs
      (\ c -> PCons (PCon c (pWilds (argsTy (dataDefs sig d) c))) qs)

usefulPWildMissCase ::
                    Signature ->
                      Name -> Either () (NonEmpty Name) -> UsefulP -> UsefulP
usefulPWildMissCase sig d h (MkUsefulP hs)
  = MkUsefulP (hs >>= usefulPWildMissCase' sig d h)

instance Usefulness UsefulP where
    nilOkCase sig nonEmptyAxiom = usefulPNilOkCase
    orCase sig nonEmptyAxiom = usefulPOrCase
    conCase sig nonEmptyAxiom d c = usefulPConCase sig d c
    wildMissCase sig nonEmptyAxiom d = usefulPWildMissCase sig d
    wildCompCase sig nonEmptyAxiom d = usefulPWildCompCase sig d

