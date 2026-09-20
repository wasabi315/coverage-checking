module CoverageCheck.Data.List.Any.Core where

data Any p = Here p
           | There (Any p)
               deriving (Eq, Show)

