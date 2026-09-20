module CoverageCheck.Data.List.HPointwise.Core where

data HPointwise r = HNil
                  | (:>>) r (HPointwise r)
                      deriving (Eq, Show)

