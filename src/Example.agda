module @0 Example where

open import CoverageCheck

--------------------------------------------------------------------------------
-- Example from the paper

pattern `unit = 'u' ∷ 'n' ∷ 'i' ∷ 't' ∷ []
pattern `list = 'l' ∷ 'i' ∷ 's' ∷ 't' ∷ []
pattern `nil  = 'n' ∷ 'i' ∷ 'l' ∷ []
pattern `one  = 'o' ∷ 'n' ∷ 'e' ∷ []
pattern `cons = 'c' ∷ 'o' ∷ 'n' ∷ 's' ∷ []

pattern ⟨unit⟩ = `unit ⟨ InHere ⟩
pattern ⟨list⟩ = `list ⟨ InThere InHere ⟩
pattern ⟨nil⟩  = `nil ⟨ InHere ⟩
pattern ⟨one⟩  = `one ⟨ InThere InHere ⟩
pattern ⟨cons⟩ = `cons ⟨ InThere (InThere InHere) ⟩

pattern unit      = con ⟨unit⟩ ⌈⌉
pattern nil       = con ⟨nil⟩ ⌈⌉
pattern one x     = con ⟨one⟩ (x ◂ ⌈⌉)
pattern cons x xs = con ⟨cons⟩ (x ◂ xs ◂ ⌈⌉)

instance
  globals : Globals
  globals .dataScope                  = `unit ∷ `list ∷ []
  globals .freshDataScope             = (λ ()) ◂ ⌈⌉ , (⌈⌉ , tt)
  globals .conScope      (`unit ⟨ _ ⟩) = `unit ∷ []
  globals .conScope      (`list ⟨ _ ⟩) = `nil ∷ `one ∷ `cons ∷ []
  globals .freshConScope {`unit ⟨ _ ⟩} = ⌈⌉ , tt
  globals .freshConScope {`list ⟨ _ ⟩} = ((λ ()) ◂ (λ ()) ◂ ⌈⌉) , ((λ ()) ◂ ⌈⌉ , (⌈⌉ , tt))
  globals .conScope      (_ ⟨ InThere (InThere ()) ⟩)
  globals .freshConScope {_ ⟨ InThere (InThere ()) ⟩}

  -- type unit = Unit
  unitDef : {p : In `unit (dataScope globals)} → Datatype (`unit ⟨ p ⟩)
  unitDef .dataCons            = _
  unitDef .fullDataCons        = refl
  unitDef .argsTy (`unit ⟨ _ ⟩) = []
  unitDef .argsTy (_ ⟨ InThere () ⟩)

  -- type list = Nil | One unit | Cons unit list
  listDef : {p : In `list (dataScope globals)} → Datatype (`list ⟨ p ⟩)
  listDef .dataCons = _
  listDef .fullDataCons = refl
  listDef .argsTy (`nil ⟨ _ ⟩)  = []
  listDef .argsTy (`one ⟨ _ ⟩)  = TyData ⟨unit⟩ ∷ []
  listDef .argsTy (`cons ⟨ _ ⟩) = TyData ⟨unit⟩ ∷ TyData ⟨list⟩ ∷ []
  listDef .argsTy (_ ⟨ InThere (InThere (InThere ())) ⟩)

  sig : Signature
  sig .dataDefs (`unit ⟨ _ ⟩) = unitDef
  sig .dataDefs (`list ⟨ _ ⟩) = listDef
  sig .dataDefs (_ ⟨ InThere (InThere ()) ⟩)

  nonEmptyAxiom : {α : Type} → Value α
  nonEmptyAxiom {TyData (`unit ⟨ _ ⟩)} = con ⟨unit⟩ ⌈⌉
  nonEmptyAxiom {TyData (`list ⟨ _ ⟩)} = con ⟨nil⟩ ⌈⌉
  nonEmptyAxiom {TyData (_ ⟨ InThere (InThere ()) ⟩)}


P : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
P =
  (nil ◂ —   ◂ ⌈⌉) ∷
  (—   ◂ nil ◂ ⌈⌉) ∷
  []

-- P is non-exhaustive, witnessed by one unit ∷ one unit ∷ []
_ : decNonExhaustive P ≡ Right ((one unit ◂ one unit ◂ ⌈⌉) ⟨ _ ⟩)
_ = refl

Q : PatternMatrix (TyData ⟨list⟩ ∷ TyData ⟨list⟩ ∷ [])
Q =
  (nil      ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ nil      ◂ ⌈⌉) ∷
  (one —    ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ one —    ◂ ⌈⌉) ∷
  (cons — — ◂ —        ◂ ⌈⌉) ∷
  (—        ◂ cons — — ◂ ⌈⌉) ∷
  []

-- Q is exhaustive, so we get a total matching function of type `∀ vs → Match Q vs` inside the inj₁
_ : decNonExhaustive Q ≡ Left (Erased (the (∀ vs → Match Q vs) _))
_ = refl
