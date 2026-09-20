module CoverageCheck.Data.List.First.Properties where

import CoverageCheck.Data.List.First.Core (First(FHere, FThere))
import CoverageCheck.Extra.DecP (DecP(No, Yes), ifDecP, mapDecP)

firstDecP :: (a -> DecP p) -> [a] -> DecP (First p)
firstDecP f [] = No
firstDecP f (x : xs)
  = ifDecP (f x) (\ p -> Yes (FHere p))
      (mapDecP FThere (firstDecP f xs))

