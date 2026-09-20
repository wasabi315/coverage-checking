module CoverageCheck.Data.List.First.Core where

data First p = FHere p
             | FThere (First p)
                 deriving (Eq, Show)

