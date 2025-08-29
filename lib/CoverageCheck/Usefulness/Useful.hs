module CoverageCheck.Usefulness.Useful where

import CoverageCheck.Instance (splitInstances)
import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Cons, Nil), NonEmpty(MkNonEmpty), These(Both, That, This))
import CoverageCheck.Syntax (Dataty(argsTy), Signature(dataDefs), Ty, Value(VCon), Values, inhab, inhabAt)
import CoverageCheck.Usefulness.Algorithm (Usefulness)

import CoverageCheck.Usefulness.Algorithm

newtype Useful = MkUseful{witness :: Values}

usefulNilOkCase :: Useful
usefulNilOkCase = MkUseful Nil

usefulOrCase :: These Useful Useful -> Useful
usefulOrCase (This h) = h
usefulOrCase (That h) = h
usefulOrCase (Both h _) = h

usefulConCase :: Signature -> Name -> Name -> Useful -> Useful
usefulConCase sig d c (MkUseful usvs)
  = case splitInstances (argsTy (dataDefs sig d) c) usvs of
        (us, vs) -> MkUseful (Cons (VCon c us) vs)

usefulWildCompCase ::
                   Signature -> Name -> NonEmpty (Name, Useful) -> Useful
usefulWildCompCase sig d (MkNonEmpty (c, MkUseful usvs) _)
  = case splitInstances (argsTy (dataDefs sig d) c) usvs of
        (us, vs) -> MkUseful (Cons (VCon c us) vs)

usefulWildMissCase ::
                   Signature ->
                     Name ->
                       (Ty -> Value) -> Either () (NonEmpty Name) -> Useful -> Useful
usefulWildMissCase sig d nonEmptyAxiom (Left ()) (MkUseful vs)
  = MkUseful (Cons (inhab sig nonEmptyAxiom d) vs)
usefulWildMissCase sig d nonEmptyAxiom (Right (MkNonEmpty c _))
  (MkUseful vs) = MkUseful (Cons (inhabAt sig nonEmptyAxiom d c) vs)

instance Usefulness Useful where
    nilOkCase sig nonEmptyAxiom = usefulNilOkCase
    orCase sig nonEmptyAxiom = usefulOrCase
    conCase sig nonEmptyAxiom d c = usefulConCase sig d c
    wildMissCase sig nonEmptyAxiom d
      = usefulWildMissCase sig d nonEmptyAxiom
    wildCompCase sig nonEmptyAxiom d = usefulWildCompCase sig d

