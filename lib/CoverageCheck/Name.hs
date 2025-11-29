module CoverageCheck.Name where

import CoverageCheck.Prelude (DecP(No), mapDecP, these, theseDecP)
import Data.List.NonEmpty (NonEmpty((:|)), (<|))

type Name = String

anyNameIn' :: (Name -> Bool) -> [Name] -> Bool
anyNameIn' f [] = False
anyNameIn' f (x : ys) = f x || anyNameIn' f ys

decPAnyNameIn ::
              [Name] -> (Name -> DecP p) -> DecP (NonEmpty (Name, p))
decPAnyNameIn [] f = No
decPAnyNameIn (x : xs) f
  = mapDecP (these (\ h -> (x, h) :| []) id (\ h hs -> (x, h) <| hs))
      (theseDecP (f x) (decPAnyNameIn xs (\ y -> f y)))

