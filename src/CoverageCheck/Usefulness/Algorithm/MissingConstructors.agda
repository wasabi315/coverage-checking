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

  infix 4 _∈_ _∉_ _∈ˢ_ _∉ˢ_ _∈ˢᵐ_ _∉ˢᵐ_

  -- Does c appear in the set of root constructors of p?
  _∈_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∈ —         = ⊥
  c ∈ con c' ps = c ≡ c'
  c ∈ (p ∣ q)   = Either (c ∈ p) (c ∈ q)

  _∉_ : NameCon d0 → Pattern (TyData d0) → Type
  c ∉ p = ¬ c ∈ p

  _∈ˢ_ _∉ˢ_ : NameCon d0 → PatternStack ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈ˢ pss = c ∈ headAll (headAll pss)
  c ∉ˢ pss = c ∉ headAll (headAll pss)

  _∈ˢᵐ_ _∉ˢᵐ_ : NameCon d0 → PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0) → Type
  c ∈ˢᵐ psmat = Any (c ∈ˢ_) psmat
  c ∉ˢᵐ psmat = All (c ∉ˢ_) psmat

-- Relation between _∈_ and operations on rootConSet

module @0 _ ⦃ @0 sig : Signature ⦄ {@0 d0} (@0 c : NameCon d0) where

  memberRootConSet' : (p : Pattern (TyData d0))
    → Reflects (c ∈ p) (Set.member c (rootConSet' p))
  memberRootConSet' — rewrite prop-member-empty c = id
  memberRootConSet' (con c' _)
    rewrite prop-member-singleton c c'
    = isEquality c c'
  memberRootConSet' (p ∣ q)
    rewrite prop-member-union c (rootConSet' p) (rootConSet' q)
    = eitherReflects (memberRootConSet' p) (memberRootConSet' q)

  memberRootConSet : (psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (c ∈ˢᵐ psmat) (Set.member c (rootConSet psmat))
  memberRootConSet [] rewrite prop-member-empty c = λ ()
  memberRootConSet (pss ∷ psss)
    rewrite prop-member-union c (rootConSet' (headAll (headAll pss))) (rootConSet psss)
    = mapReflects
        (either here there)
        (λ where (here h) → Left h; (there h) → Right h)
        (eitherReflects
          (memberRootConSet' (headAll (headAll pss)))
          (memberRootConSet psss))


module @0 _ ⦃ @0 sig : Signature ⦄
  {@0 d0} (@0 c : NameCon d0)
  (@0 psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0))
  (let conSet     = rootConSet psmat
       missConSet = Set.difference (nameConSet (dataDefs sig d0)) conSet)
  where

  notMemberMissConSet : Reflects (c ∈ˢᵐ psmat) (not (Set.member c missConSet))
  notMemberMissConSet
    rewrite prop-member-difference c (nameConSet (dataDefs sig d0)) conSet
    | nameConSet-universal (dataDefs sig d0) c
    | not-not (Set.member c conSet)
    = memberRootConSet c psmat

  memberMissConSet : Reflects (c ∉ˢᵐ psmat) (Set.member c missConSet)
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

  nullRootConSet
    : (psmat : PatternStackMatrix ((TyData d0 ∷ αs0) ∷ αss0))
    → Reflects (∀ c → c ∉ˢᵐ psmat) (Set.null (rootConSet psmat))
  nullRootConSet []
    rewrite prop-null-empty {NameCon d0} ⦃ iOrdNameIn ⦄
    = λ _ → []
  nullRootConSet (pss ∷ psmat)
    rewrite prop-null-union (rootConSet' (headAll (headAll pss))) (rootConSet psmat)
    = mapReflects
        {a = (∀ c → c ∉ˢ pss) × (∀ c → c ∉ˢᵐ psmat)}
        {b = (∀ c → c ∉ˢᵐ (pss ∷ psmat))}
        (λ (h , h') c → h c ∷ h' c)
        (λ h → (λ c → headAll (h c)) , (λ c → tailAll (h c)))
        (tupleReflects
          (nullRootConSet' (headAll (headAll pss)))
          (nullRootConSet psmat))

--------------------------------------------------------------------------------

module _ ⦃ sig : Signature ⦄ {d : NameData} where

  -- Evidence-producing version of existMissCon
  -- The result is either:
  --   1. No missing constructors (complete root constructor set)
  --   2. All constructors are missing (empty root constructor set)
  --   3. Some constructors are missing
  decExistMissCon
    : (psmat : PatternStackMatrix ((TyData d ∷ αs0) ∷ αss0))
    → Either (Erase (∀ c → c ∈ˢᵐ psmat))
        (Either
          (Erase (∀ c → c ∉ˢᵐ psmat))
          (NonEmpty (∃[ c ∈ NameCon d ] c ∉ˢᵐ psmat)))
  decExistMissCon psmat = case toAscNonEmptyW missConSet of λ where
      (Left (Erased empty)) →
        Left (Erased λ c →
          extractTrue ⦃ cong not (empty c) ⦄ (notMemberMissConSet c psmat))
      (Right misses) →
        Right (if Set.null conSet
          then Left (Erased (extractTrue (nullRootConSet psmat)))
          else Right (mapNonEmptyRefine (λ miss →
                extractTrue ⦃ miss ⦄ (memberMissConSet _ psmat)) misses))
    where
      conSet     = rootConSet psmat
      missConSet = Set.difference (nameConSet (dataDefs sig d)) conSet
  {-# COMPILE AGDA2HS decExistMissCon #-}
