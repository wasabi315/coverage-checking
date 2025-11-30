open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import Data.Set as Set using (Set)
open import Haskell.Data.List.NonEmpty using (NonEmpty)

open import CoverageCheck.Usefulness.Algorithm.Types
open import CoverageCheck.Usefulness.Algorithm.Raw

module CoverageCheck.Usefulness.Algorithm.MissingConstructors
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    d : NameData
    @0 αs0 : Tys
    @0 αss0 : TyStack

--------------------------------------------------------------------------------

module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} where

  infix 4 _∈_ _∉_ _∈*_ _∉*_ _∈**_ _∉**_

  -- Does c appear in the set of root constructors of p?
  _∈_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∈ —         = ⊥
  c ∈ con c' ps = c ≡ c'
  c ∈ (p ∣ q)   = Either (c ∈ p) (c ∈ q)

  _∉_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∉ p = ¬ c ∈ p

  _∈*_ _∉*_ : NameCon d0 → PatternStack ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈* pss = c ∈ headPattern (headAll pss)
  c ∉* pss = c ∉ headPattern (headAll pss)

  _∈**_ _∉**_ : NameCon d0 → PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈** psss = Any (c ∈*_) psss
  c ∉** psss = All (c ∉*_) psss


module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} (@0 c : NameCon d0) where

  memberRootConSet' : (p : Pattern (TyData d0))
    → Reflects (c ∈ p) (Set.member c (rootConSet' p))
  memberRootConSet' — rewrite prop-member-empty c = id
  memberRootConSet' (con c' _) rewrite prop-member-singleton c c' = isEquality c c'
  memberRootConSet' (p ∣ q)
    rewrite prop-member-union c (rootConSet' p) (rootConSet' q)
    = eitherReflects (memberRootConSet' p) (memberRootConSet' q)

  memberRootConSet : (psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (c ∈** psss) (Set.member c (rootConSet psss))
  memberRootConSet [] rewrite prop-member-empty c = λ ()
  memberRootConSet (pss ∷ psss)
    rewrite prop-member-union c (rootConSet' (headPattern (headAll pss))) (rootConSet psss)
    = mapReflects
        (either here there)
        (λ where (here h) → Left h; (there h) → Right h)
        (eitherReflects (memberRootConSet' (headPattern (headAll pss))) (memberRootConSet psss))


module @0 _ ⦃ @0 sig : Signature ⦄
  {@0 d0} (@0 c : NameCon d0) (@0 psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
  (let conSet     = rootConSet psss
       missConSet = Set.difference (universalNameConSet (dataDefs sig d0)) conSet)
  where

  notMemberMissConSet : Reflects (c ∈** psss) (not (Set.member c missConSet))
  notMemberMissConSet
    rewrite prop-member-difference c (universalNameConSet (dataDefs sig d0)) conSet
    | universalNameConSetUniversal (dataDefs sig d0) c
    | not-not (Set.member c conSet)
    = memberRootConSet c psss

  memberMissConSet : Reflects (c ∉** psss) (Set.member c missConSet)
  memberMissConSet rewrite sym (not-not (Set.member c missConSet)) =
    mapReflects (¬Any⇒All¬ _) All¬⇒¬Any (negReflects notMemberMissConSet)


module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} where

  nullRootConSet' : (p : Pattern (TyData d0))
    → Reflects (∀ c → c ∉ p) (Set.null (rootConSet' p))
  nullRootConSet' —
    rewrite prop-null-empty {NameCon d0} ⦃ iOrdNameIn ⦄
    = λ _ → id
  nullRootConSet' (con c _)
    rewrite prop-null-insert c Set.empty
    = λ h → h c refl
  nullRootConSet' (p ∣ q)
    rewrite prop-null-union (rootConSet' p) (rootConSet' q)
    = mapReflects
        {a = (∀ c → c ∉ p) × (∀ c → c ∉ q)}
        {b = (∀ c → c ∉ (p ∣ q))}
        (λ (h , h') c → either (h c) (h' c))
        (λ h → (λ c → h c ∘ Left) , (λ c → h c ∘ Right))
        (tupleReflects (nullRootConSet' p) (nullRootConSet' q))

  nullRootConSet : (psss : PatternMatrixStack ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (∀ c → c ∉** psss) (Set.null (rootConSet psss))
  nullRootConSet []
    rewrite prop-null-empty {NameCon d0} ⦃ iOrdNameIn ⦄
    = λ c → []
  nullRootConSet (pss ∷ psss)
    rewrite prop-null-union (rootConSet' (headPattern (headAll pss))) (rootConSet psss)
    = mapReflects
        {a = (∀ c → c ∉* pss) × (∀ c → c ∉** psss)}
        {b = (∀ c → c ∉** (pss ∷ psss))}
        (λ (h , h') c → h c ∷ h' c)
        (λ h → (λ c → headAll (h c)) , (λ c → tailAll (h c)))
        (tupleReflects (nullRootConSet' (headPattern (headAll pss))) (nullRootConSet psss))

--------------------------------------------------------------------------------

module _ ⦃ sig : Signature ⦄ {d : NameData} where

  -- Are there constructors that does not appear in the first column of P?
  decExistMissCon : (P : PatternMatrixStack ((TyData d ∷ αs0) ∷ αss0))
    → Either (Erase (∀ c → c ∈** P))
        (Either (Erase (∀ c → c ∉** P)) (NonEmpty (∃[ c ∈ NameCon d ] c ∉** P)))
  decExistMissCon psss = case toAscNonEmptyW missConSet of λ where
      (Left (Erased empty)) →
        Left (Erased λ c → extractTrue ⦃ cong not (empty c) ⦄ (notMemberMissConSet c psss))
      (Right misses) → Right (if Set.null conSet
        then Left (Erased (extractTrue (nullRootConSet psss)))
        else Right (mapNonEmptyRefine (λ miss → extractTrue ⦃ miss ⦄ (memberMissConSet _ psss)) misses))
    where
      conSet missConSet : Set (NameCon d)
      conSet     = rootConSet psss
      missConSet = Set.difference (universalNameConSet (dataDefs sig d)) conSet
  {-# COMPILE AGDA2HS decExistMissCon #-}
