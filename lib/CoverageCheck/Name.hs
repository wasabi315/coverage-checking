module CoverageCheck.Name where

import CoverageCheck.Prelude (DecP(No), mapDecP, these, theseDecP)
import Data.List.NonEmpty (NonEmpty((:|)), (<|))
import Data.Set (Set)
import qualified Data.Set (empty, insert)

type Name = String

data Scope = SNil
           | SCons Name Scope

allNameInSet' :: Scope -> Set Name
allNameInSet' SNil = Data.Set.empty
allNameInSet' (SCons x xs) = Data.Set.insert x (allNameInSet' xs)

anyNameIn' :: (Name -> Bool) -> Scope -> Bool
anyNameIn' f SNil = False
anyNameIn' f (SCons x ys) = f x || anyNameIn' f ys

decPAnyNameIn ::
              Scope -> (Name -> DecP p) -> DecP (NonEmpty (Name, p))
decPAnyNameIn SNil f = No
decPAnyNameIn (SCons x xs) f
  = mapDecP (these (\ h -> (x, h) :| []) id (\ h hs -> (x, h) <| hs))
      (theseDecP (f x) (decPAnyNameIn xs (\ y -> f y)))

