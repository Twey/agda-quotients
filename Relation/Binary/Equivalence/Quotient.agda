open import Relation.Binary

module Relation.Binary.Equivalence.Quotient {α} {ℓ₁} {ℓ₂} {A : Set α}
  (_≈₁_ : Rel A ℓ₁)
  (_≈₂_ : Rel A ℓ₂)
  (eq₁ : IsEquivalence _≈₁_)
  (eq₂ : IsEquivalence _≈₂_)
  where

open import Level
open import Data.Product
open import Data.Bool

data Union : Rel (Bool × A) (α ⊔ ℓ₁ ⊔ ℓ₂) where
  inj₁ : ∀ {x y} → x ≈₁ y → Union (false , x) (true  , y)
  inj₂ : ∀ {x y} → x ≈₂ y → Union (true  , x) (false , y)
  
data _≈′_ : Rel A (ℓ₁ ⊔ ℓ₂) where
  
