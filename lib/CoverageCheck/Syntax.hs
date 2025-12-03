module CoverageCheck.Syntax where

import CoverageCheck.Name (Name, Scope)
import CoverageCheck.Prelude (All(Nil, (:>)))

data Ty = TyData Name
            deriving Show

type Tys = [Ty]

data Dataty = Dataty{argsTy :: Name -> Tys, dataCons :: Scope}

newtype Signature = Signature{dataDefs :: Name -> Dataty}

data Value = VCon Name Values
               deriving (Show, Eq)

type Values = All Value

tabulateValues :: Tys -> (Ty -> Value) -> Values
tabulateValues [] f = Nil
tabulateValues (α : αs) f = f α :> tabulateValues αs f

data Pattern = PWild
             | PCon Name Patterns
             | POr Pattern Pattern
                 deriving (Show, Eq)

type Patterns = All Pattern

pWilds :: Tys -> Patterns
pWilds [] = Nil
pWilds (α : αs) = PWild :> pWilds αs

only :: Value -> Pattern
only (VCon c vs) = PCon c (onlys vs)

onlys :: Values -> Patterns
onlys Nil = Nil
onlys (v :> vs) = only v :> onlys vs

