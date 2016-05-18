module Relation.Binary.Quotient where

import Relation.Binary as RB
import Relation.Binary.Equivalence as RBE
import Relation.Binary.Quotient.Core as Core

open import Level

_//_ : ∀ {α} {A : Set α} {ℓ₁ ℓ₂}
     → RB.Rel A ℓ₁
     → RB.Rel A ℓ₂
     → RB.Rel A (α ⊔ ℓ₁ ⊔ ℓ₂)
∼₁ // ∼₂ = _∼_
  where open Core ∼₁ ∼₂

_//ᵉ_ : ∀ {α} {A : Set α} {ℓ₁ ℓ₂}
  → RBE.Equivalence A ℓ₁
  → RBE.Equivalence A ℓ₂
  → RBE.Equivalence A (α ⊔ ℓ₁ ⊔ ℓ₂)
≈₁ //ᵉ ≈₂ = record { _≈_ = _; isEquivalence = isEquivalence }
  where
    module E₁ = RBE.Equivalence ≈₁
    module E₂ = RBE.Equivalence ≈₂
    open Core.Equivalence E₁._≈_ E₂._≈_ E₁.sym E₂.sym
  
_//ˢ_ : ∀ {α ℓ ℓ′}
     → (S : RB.Setoid α ℓ)
     → RBE.Equivalence (RB.Setoid.Carrier S) ℓ′
     → RB.Setoid α (α ⊔ ℓ ⊔ ℓ′)
S //ˢ ≈ = Core.Equivalence.setoid S._≈_ E._≈_ S.sym E.sym
  where
    module S = RB.Setoid S
    module E = RBE.Equivalence ≈
