module CoverageCheck.Name where

import CoverageCheck.Prelude (DecP(No), mapDecP, these, theseDecP)
import Data.List.NonEmpty (NonEmpty((:|)), (<|))
import Data.Set (Set)
import qualified Data.Set (empty, insert)

type Name = String

data Scope = SNil
           | SCons Name Scope

nameInSet' :: Scope -> Set Name
nameInSet' SNil = Data.Set.empty
nameInSet' (SCons x xs) = Data.Set.insert x (nameInSet' xs)

anyNameIn' :: Scope -> (Name -> Bool) -> Bool
anyNameIn' SNil f = False
anyNameIn' (SCons x ys) f = f x || anyNameIn' ys f

decPAnyNameIn ::
              Scope -> (Name -> DecP p) -> DecP (NonEmpty (Name, p))
decPAnyNameIn SNil f = No
decPAnyNameIn (SCons x xs) f
  = mapDecP (these (\ h -> (x, h) :| []) id (\ h hs -> (x, h) <| hs))
      (theseDecP (f x) (decPAnyNameIn xs (\ y -> f y)))

