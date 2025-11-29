module CoverageCheck.Usefulness.Definition where

import CoverageCheck.Prelude (All)
import CoverageCheck.Syntax (Patterns)
import Data.List.NonEmpty (NonEmpty)

newtype Useful = MkUseful{witnesses :: NonEmpty (All Patterns)}

