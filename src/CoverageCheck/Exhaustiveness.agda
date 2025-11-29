open import CoverageCheck.Prelude
open import CoverageCheck.GlobalScope using (Globals)
open import CoverageCheck.Instance
open import CoverageCheck.Subsumption
open import CoverageCheck.Syntax
open import CoverageCheck.Name
open import CoverageCheck.Usefulness

open import Haskell.Data.List.NonEmpty as NonEmpty using (NonEmpty; _∷_)

module CoverageCheck.Exhaustiveness
  ⦃ @0 globals : Globals ⦄
  where

private open module @0 G = Globals globals

private
  variable
    α β : Ty
    αs βs : Tys
    d : NameData
    @0 α0 β0 : Ty
    @0 αs0 βs0 : Tys
    @0 d0 : NameData

--------------------------------------------------------------------------------
-- Exhaustiveness

module _ ⦃ @0 sig : Signature ⦄ where

  -- There is a matching row in P for every list of values
  Exhaustive : PatternMatrix αs0 → Type
  Exhaustive P = ∀ vs → Match P vs

  -- There is a list of patterns that has at least one instance and whose instances do not match any row in P
  NonExhaustive' : PatternMatrix αs0 → Type
  NonExhaustive' P = ∃[ ps ∈ _ ] (∃[ vs ∈ _ ] ps ≼* vs) × (∀ {vs} → ps ≼* vs → ¬ Match P vs)
  {-# COMPILE AGDA2HS NonExhaustive' inline #-}

  NonExhaustive : PatternMatrix αs0 → Type
  NonExhaustive P = NonEmpty (NonExhaustive' P)
  {-# COMPILE AGDA2HS NonExhaustive inline #-}

  -- non-exhaustiveness defined in terms of usefulness:
  -- P is non-exhaustive if —* is useful with respect to P
  NonExhaustiveU : PatternMatrix αs0 → Type
  NonExhaustiveU P = Useful (map (_∷ []) P) (—* ∷ [])
  {-# COMPILE AGDA2HS NonExhaustiveU inline #-}

  -- P is exhaustive if —* is not useful with respect to P
  ExhaustiveU : PatternMatrix αs0 → Type
  ExhaustiveU P = ¬ NonExhaustiveU P

  module _ {@0 P : PatternMatrix αs0} where

    nonExhaustiveUToNonExhaustive' : Useful' (map (_∷ []) P) (—* ∷ []) → NonExhaustive' P
    nonExhaustiveUToNonExhaustive' = λ where
      ⟪ qs ∷ [] , is ∷ [] , disj , _ ⟫ →
        qs ⟨ (_ ⟨ is ⟩) , (λ is ms → disj (gmapAny⁺ (_∷ []) (firstToAny ms)) (is ∷ [])) ⟩
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive' inline #-}

    nonExhaustiveUToNonExhaustive :
        NonEmpty (Useful' (map (_∷ []) P) (—* ∷ []))
      → NonExhaustive P
    nonExhaustiveUToNonExhaustive = fmap nonExhaustiveUToNonExhaustive'
    {-# COMPILE AGDA2HS nonExhaustiveUToNonExhaustive inline #-}

    @0 nonExhaustiveToNonExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → NonExhaustive P → NonExhaustiveU P
    nonExhaustiveToNonExhaustiveU hs =
      MkUseful (flip fmap hs λ (qs ⟨ is , h ⟩) →
        ⟪ qs ∷ []
        , proof is ∷ []
        , (λ where
             isss (is ∷ []) →
               notFirstToNotAny (h is) (gmapAny⁻ (λ where (iss ∷ _) → iss) isss))
        , —⊆* ∷ []
        ⟫)

    @0 exhaustiveToExhaustiveU : ⦃ nonEmptyAxiom : ∀ {α} → Value α ⦄
      → Exhaustive P → ExhaustiveU P
    exhaustiveToExhaustiveU h (MkUseful (⟪ qs ∷ [] , _ , disj , _ ⟫ ∷ _)) =
      contradiction (gmapAny⁺ (_∷ []) (firstToAny (h (insts qs)))) (flip disj (inst≼* qs ∷ []))


  module @0 _ {P : PatternMatrix αs0} where

    exhaustiveUToExhaustive : ExhaustiveU P → Exhaustive P
    exhaustiveUToExhaustive h vs =
      case decMatch P vs of λ where
        (Yes h') → h'
        (No h')  →
          contradiction
            (MkUseful
              (⟪ onlys vs ∷ []
              , only≼* vs ∷ []
              , (λ where
                    isss (is ∷ []) →
                      let iss = gmapAny⁻ (λ where (iss ∷ _) → iss) isss
                          iss' = subst (λ vs → P ≼** vs) (sym (only≼*⇒≡ is)) iss
                       in notFirstToNotAny h' iss'
                  )
              , —⊆* ∷ [] ⟫ ∷ []))
            h

--------------------------------------------------------------------------------
-- Entrypoint

module _ ⦃ sig : Signature ⦄ ⦃ @0 nonEmptyAxiom : ∀ {α} → Value α ⦄ where

  decNonExhaustive : (pss : PatternMatrix αs) → Either (Erase (Exhaustive pss)) (NonExhaustive pss)
  decNonExhaustive pss = ifDecP (decUseful pss pWilds)
    (λ ⦃ h ⦄ → Right (nonExhaustiveUToNonExhaustive (h .witnesses)))
    (λ ⦃ h ⦄ → Left (Erased (exhaustiveUToExhaustive h)))
  {-# COMPILE AGDA2HS decNonExhaustive #-}
