open import Relation.Binary

module Data.Thrist {o ll} {A : Set o} (R : Rel A ll) where

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

-- >> defn
infixl 4 _,_
data Thrist : Rel A (o ⊔ ll) where
  ⊘ : ∀ {x} → Thrist x x
  _,_ : ∀ {i j k} → Thrist i j → R j k → Thrist i k
-- <<

[_] : ∀ {i j : A} → R i j → Thrist i j
[ r ] = ⊘ , r

-- >> trans
_++_ : Transitive Thrist
xs ++ ⊘        = xs
xs ++ (ys , y) = (xs ++ ys) , y
-- <<

-- >> assoc
++-assoc : ∀ {i j k l}
    (xs : Thrist i j) (ys : Thrist j k) (zs : Thrist k l)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys ⊘ = refl
++-assoc xs ys (zs , z) rewrite ++-assoc xs ys zs = refl
-- <<

-- >> symm
reverse : Symmetric R → Symmetric Thrist
reverse symmetric ⊘        = ⊘
reverse symmetric (xs , x) = [ symmetric x ] ++ reverse symmetric xs
-- <<

-- >> id
identityʳ : ∀ {i j} → (xs : Thrist i j) → ⊘ ++ xs ≡ xs
identityʳ ⊘ = refl
identityʳ (xs , x) rewrite identityʳ xs = refl
-- <<
