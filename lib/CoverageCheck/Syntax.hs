module CoverageCheck.Syntax where

import CoverageCheck.Name (Name, Scope)
import CoverageCheck.Prelude (All(Nil, (:>)))

data Ty = TyData Name
            deriving Show

type Tys = [Ty]

data Dataty = Dataty{dataCons :: Scope, argsTy :: Name -> Tys}

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

headPattern :: Patterns -> Pattern
headPattern (p :> _) = p

tailPatterns :: Patterns -> Patterns
tailPatterns (_ :> ps) = ps

only :: Value -> Pattern
only (VCon c vs) = PCon c (onlys vs)

onlys :: Values -> Patterns
onlys Nil = Nil
onlys (v :> vs) = only v :> onlys vs

inhab' :: Signature -> (Ty -> Value) -> Name -> (Name, Values)
inhab' sig nonEmptyAxiom d
  = case nonEmptyAxiom (TyData d) of
        VCon c vs -> (c, vs)

inhab :: Signature -> (Ty -> Value) -> Name -> Value
inhab sig nonEmptyAxiom d
  = VCon (fst (inhab' sig nonEmptyAxiom d))
      (snd (inhab' sig nonEmptyAxiom d))

inhabAt :: Signature -> (Ty -> Value) -> Name -> Name -> Value
inhabAt sig nonEmptyAxiom d c
  = VCon c
      (tabulateValues (argsTy (dataDefs sig d) c)
         (\ α -> nonEmptyAxiom α))

