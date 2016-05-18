open import Relation.Binary

module Relation.Binary.Quotient.Core {α} {ℓ₁} {ℓ₂} {A : Set α}
  (_∼₁_ : Rel A ℓ₁)
  (_∼₂_ : Rel A ℓ₂)
  where


open import Level
open import Data.Sum

Union : Rel A (ℓ₁ ⊔ ℓ₂)
Union x y = x ∼₁ y ⊎ x ∼₂ y

open import Data.Thrist Union

_∼_ : Rel A (α ⊔ ℓ₁ ⊔ ℓ₂)
_∼_ = Thrist

open import Function

∼₁⇒∼ : _∼₁_ ⇒ _∼_
∼₁⇒∼ = [_] ∘ inj₁

∼₂⇒∼ : _∼₂_ ⇒ _∼_
∼₂⇒∼ = [_] ∘ inj₂

module Equivalence
  (sym₁ : Symmetric _∼₁_)
  (sym₂ : Symmetric _∼₂_)
  where

  isEquivalence : IsEquivalence _∼_
  isEquivalence = record
    { refl  = []
    ; sym   = reverse [ inj₁ ∘ sym₁ , inj₂ ∘ sym₂ ]
    ; trans = _++_
    }

  open IsEquivalence isEquivalence public

  setoid : Setoid α (α ⊔ ℓ₁ ⊔ ℓ₂)
  setoid = record { Carrier = A; _≈_ = _∼_; isEquivalence = isEquivalence }

