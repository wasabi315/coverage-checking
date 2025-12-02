module CoverageCheck.Usefulness.Algorithm.MissingConstructors where

import CoverageCheck.Name (Name, nameInSet')
import CoverageCheck.Prelude (All)
import CoverageCheck.Syntax (Dataty(dataCons), Patterns, Signature(dataDefs))
import CoverageCheck.Usefulness.Algorithm.Raw (rootConSet)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Set (Set)
import qualified Data.Set (difference, null, toAscList)

decExistMissCon ::
                Signature ->
                  Name -> [All Patterns] -> Either () (Either () (NonEmpty Name))
decExistMissCon sig d psss
  = case
      case Data.Set.toAscList missConSet of
          [] -> Left ()
          x : xs -> Right (x :| xs)
      of
        Left () -> Left ()
        Right misses -> Right
                          (if Data.Set.null conSet then Left () else Right misses)
  where
    conSet :: Set Name
    conSet = rootConSet psss
    missConSet :: Set Name
    missConSet
      = Data.Set.difference (nameInSet' (dataCons (dataDefs sig d)))
          conSet

