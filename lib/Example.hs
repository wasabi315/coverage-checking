{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module Example where

import CoverageCheck.Exhaustiveness
import CoverageCheck.Prelude
import CoverageCheck.Syntax
import CoverageCheck.Usefulness.Useful

--------------------------------------------------------------------------------

unitDef :: Datatype
unitDef =
  Datatype
    { dataCons = ["()"],
      argsTy = \case
        "()" -> []
    }

pattern Unit :: Value
pattern Unit = VCon "()" VNil

pattern UnitP :: Pattern
pattern UnitP = PCon "()" PNil

listDef :: Datatype
listDef =
  Datatype
    { dataCons = ["Nil", "One", "Cons"],
      argsTy = \case
        "Nil" -> []
        "One" -> [TyData "Unit"]
        "Cons" -> [TyData "Unit", TyData "List"]
    }

pattern Nil :: Value
pattern Nil = VCon "Nil" VNil

pattern NilP :: Pattern
pattern NilP = PCon "Nil" PNil

pattern One :: Value -> Value
pattern One x = VCon "One" (VCons x VNil)

pattern OneP :: Pattern -> Pattern
pattern OneP p = PCon "One" (PCons p PNil)

pattern Cons :: Value -> Value -> Value
pattern Cons x xs = VCon "Cons" (VCons x (VCons xs VNil))

pattern ConsP :: Pattern -> Pattern -> Pattern
pattern ConsP p q = PCon "Cons" (PCons p (PCons q PNil))

signature :: Signature
signature =
  Signature
    { dataDefs = \case
        "Unit" -> unitDef
        "List" -> listDef
    }

nonEmptyAxiom :: Type -> Value
nonEmptyAxiom = \case
  TyData "Unit" -> Unit
  TyData "List" -> Nil

types :: Types
types = [TyData "List", TyData "List"]

example1 :: [Patterns]
example1 =
  [ NilP `PCons` (PWild `PCons` PNil),
    PWild `PCons` (NilP `PCons` PNil)
  ]

-- >>> nonExhaustiveness1 == Right (Cons Unit Nil `VCons` (Cons Unit Nil `VCons` VNil))
-- True
nonExhaustiveness1 :: Either () Values
nonExhaustiveness1 = decNonExhaustive signature nonEmptyAxiom types example1

example2 :: [Patterns]
example2 =
  [ NilP `PCons` (PWild `PCons` PNil),
    PWild `PCons` (NilP `PCons` PNil),
    OneP PWild `PCons` (PWild `PCons` PNil),
    PWild `PCons` (OneP PWild `PCons` PNil),
    ConsP PWild PWild `PCons` (PWild `PCons` PNil),
    PWild `PCons` (ConsP PWild PWild `PCons` PNil)
  ]

-- >>> nonExhaustiveness2 == Left ()
-- True
nonExhaustiveness2 :: Either () Values
nonExhaustiveness2 = decNonExhaustive signature nonEmptyAxiom types example2
