module CoverageCheck.Data.List.Many.Core where

data Many p = MNil
            | MHere p (Many p)
            | MThere (Many p)
                deriving (Eq, Show)

tailMany :: Many p -> Many p
tailMany (MHere _ ps) = ps
tailMany (MThere ps) = ps

