module CoverageCheck.Data.List.Many.Properties where

import CoverageCheck.Data.List.Many.Core (Many(MHere, MNil, MThere))
import CoverageCheck.Extra.DecP (DecP(Yes), ifDecP, mapDecP)

manyDecP :: (a -> DecP p) -> [a] -> DecP (Many p)
manyDecP f [] = Yes MNil
manyDecP f (x : xs)
  = ifDecP (f x) (\ px -> mapDecP (MHere px) (manyDecP f xs))
      (mapDecP MThere (manyDecP f xs))

