module Relation.Binary.Equivalence where

open import Relation.Binary

open import Level

record Equivalence {α} (A : Set α) ℓ : Set (α ⊔ suc ℓ) where
  field
    _≈_           : Rel A ℓ
    isEquivalence : IsEquivalence _≈_

  setoid : Setoid α ℓ
  setoid = record { Carrier = A; _≈_ = _≈_; isEquivalence = isEquivalence }

  open Setoid setoid public hiding (_≈_; isEquivalence)

of-setoid : ∀ {α ℓ} → (S : Setoid α ℓ) → Equivalence (Setoid.Carrier S) ℓ
of-setoid S = record { _≈_ = _≈_; isEquivalence = isEquivalence }
  where open Setoid S
