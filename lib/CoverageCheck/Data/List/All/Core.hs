module CoverageCheck.Data.List.All.Core where

data All p = Nil
           | (:>) p (All p)
               deriving (Eq, Show)

headAll :: All p -> p
headAll (p :> _) = p

tailAll :: All p -> All p
tailAll (_ :> ps) = ps

