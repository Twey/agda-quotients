open import Relation.Binary

module Data.Thrist {o ℓ} {A : Set o} (R : Rel A ℓ) where

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

infixl 4 _∷_
data Thrist : Rel A (o ⊔ ℓ) where
  []  : ∀ {x} → Thrist x x
  _∷_ : ∀ {i j k} → R i j → Thrist j k → Thrist i k

[_] : ∀ {i j : A} → R i j → Thrist i j
[ r ] = r ∷ []

_++_ : Transitive Thrist
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {i j k l}
    (xs : Thrist i j) (ys : Thrist j k) (zs : Thrist k l)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

reverse : Symmetric R → Symmetric Thrist
reverse symmetric [] = []
reverse symmetric (x ∷ xs) = reverse symmetric xs ++ [ symmetric x ]

identityʳ : ∀ {i j} → (xs : Thrist i j) → [] ++ xs ≡ xs
identityʳ [] = refl
identityʳ (x ∷ xs) rewrite identityʳ xs = refl

