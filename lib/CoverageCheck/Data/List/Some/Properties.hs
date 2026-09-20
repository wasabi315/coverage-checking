module CoverageCheck.Data.List.Some.Properties where

import CoverageCheck.Data.List.Many.Properties (manyDecP)
import CoverageCheck.Data.List.Some.Core (Some(SHere, SThere))
import CoverageCheck.Extra.DecP (DecP(No), ifDecP, mapDecP)

someDecP :: (a -> DecP p) -> [a] -> DecP (Some p)
someDecP f [] = No
someDecP f (x : xs)
  = ifDecP (f x) (\ px -> mapDecP (SHere px) (manyDecP f xs))
      (mapDecP SThere (someDecP f xs))

