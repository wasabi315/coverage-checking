module CoverageCheck.Usefulness.Useful where

import CoverageCheck.Name (Name)
import CoverageCheck.Prelude (All(Nil, (:>)), These(Both, That, This))
import CoverageCheck.Syntax (Signature, Ty, Value(VCon), Values, inhab, inhabAt)
import CoverageCheck.Usefulness.Algorithm (Usefulness)
import Data.List.NonEmpty (NonEmpty((:|)))

import CoverageCheck.Usefulness.Algorithm

newtype Useful = MkUseful{witness :: All Values}

usefulNilOkCase :: Useful
usefulNilOkCase = MkUseful Nil

usefulTailCase :: Useful -> Useful
usefulTailCase (MkUseful vss) = MkUseful (Nil :> vss)

usefulOrCase :: These Useful Useful -> Useful
usefulOrCase (This h) = h
usefulOrCase (That h) = h
usefulOrCase (Both h _) = h

usefulConCase :: Name -> Useful -> Useful
usefulConCase c (MkUseful (vs' :> (vs :> vss)))
  = MkUseful ((VCon c vs' :> vs) :> vss)

usefulWildCompCase :: NonEmpty (Name, Useful) -> Useful
usefulWildCompCase ((c, MkUseful (vs' :> (vs :> vss))) :| _)
  = MkUseful ((VCon c vs' :> vs) :> vss)

usefulWildMissCase ::
                   Signature ->
                     (Ty -> Value) ->
                       Name -> Either () (NonEmpty Name) -> Useful -> Useful
usefulWildMissCase sig nonEmptyAxiom d (Left ())
  (MkUseful (vs :> vss))
  = MkUseful ((inhab sig nonEmptyAxiom d :> vs) :> vss)
usefulWildMissCase sig nonEmptyAxiom d (Right (c :| _))
  (MkUseful (vs :> vss))
  = MkUseful ((inhabAt sig nonEmptyAxiom d c :> vs) :> vss)

instance Usefulness Useful where
    nilOkCase sig nonEmptyAxiom = usefulNilOkCase
    tailCase sig nonEmptyAxiom = usefulTailCase
    orCase sig nonEmptyAxiom = usefulOrCase
    conCase sig nonEmptyAxiom d c = usefulConCase c
    wildMissCase sig nonEmptyAxiom d
      = usefulWildMissCase sig nonEmptyAxiom d
    wildCompCase sig nonEmptyAxiom d = usefulWildCompCase

