module CoverageCheck.Usefulness.Definition where

import CoverageCheck.Syntax (Patterns)
import Data.List.NonEmpty (NonEmpty)

newtype Useful = Useful{witnesses :: NonEmpty Patterns}
                   deriving (Show)

