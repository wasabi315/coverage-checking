module CoverageCheck.Syntax where

import CoverageCheck.Name (Name)

data Ty = TyData Name
            deriving Show

type Tys = [Ty]

data Dataty = Dataty{dataCons :: [Name], argsTy :: Name -> Tys}

newtype Signature = Signature{dataDefs :: Name -> Dataty}

data Value = VCon Name Values
               deriving (Show, Eq)

data Values = VNil
            | VCons Value Values
                deriving (Show, Eq)

infixr 5 `appendValues`
appendValues :: Values -> Values -> Values
appendValues VNil vs = vs
appendValues (VCons u us) vs = VCons u (appendValues us vs)

tabulateValues :: Tys -> (Ty -> Value) -> Values
tabulateValues [] f = VNil
tabulateValues (α : αs) f = VCons (f α) (tabulateValues αs f)

data Pattern = PWild
             | PCon Name Patterns
             | POr Pattern Pattern
                 deriving (Show, Eq)

data Patterns = PNil
              | PCons Pattern Patterns
                  deriving (Show, Eq)

pWilds :: Tys -> Patterns
pWilds [] = PNil
pWilds (α : αs) = PCons PWild (pWilds αs)

headPattern :: Patterns -> Pattern
headPattern (PCons p _) = p

tailPatterns :: Patterns -> Patterns
tailPatterns (PCons _ ps) = ps

infixr 5 `appendPatterns`
appendPatterns :: Patterns -> Patterns -> Patterns
appendPatterns PNil qs = qs
appendPatterns (PCons p ps) qs = PCons p (appendPatterns ps qs)

only :: Value -> Pattern
only (VCon c vs) = PCon c (onlys vs)

onlys :: Values -> Patterns
onlys VNil = PNil
onlys (VCons v vs) = PCons (only v) (onlys vs)

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

