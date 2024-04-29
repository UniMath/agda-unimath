# Standard simplices

```agda
module simplicial-type-theory.standard-simplices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.directed-relation-directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The standard simplices

$$x₁ ≥ x₂ ≥ … ≥ xₙ₋₁ ≥ xₙ$$ (in the right-associated cube)

```text
subtype-Δ : (n : ℕ) → subtype lzero (simplicial-cube n)
subtype-Δ 0 _ = unit-Prop
subtype-Δ 1 _ = unit-Prop
subtype-Δ 2 (x , y) = leq-𝟚-Prop y x
subtype-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , y , u) =
  conj-Prop (subtype-Δ 2 (x , y)) (subtype-Δ (succ-ℕ (succ-ℕ n)) (y , u))

predicate-Δ = is-in-subtype ∘ subtype-Δ

Δ = type-subtype ∘ subtype-Δ
```

### The boundary of the standard simplices

```agda
-- -- Auxillary function defining the faces of Δ except for the first one
-- aux-face-Δ̬ : (n r : ℕ) → Shape (simplicial-cube n)
-- aux-face-Δ̬ 0 _ _ = ⊥ᵥ
-- aux-face-Δ̬ 1 0 x = x =̬ 0₂
-- aux-face-Δ̬ 1 (succ-ℕ _) x = ⊥ᵥ
-- aux-face-Δ̬ 2 0 (x , y) = x =̬ y
-- aux-face-Δ̬ 2 (succ-ℕ r) (x , y) = aux-face-Δ̬ 1 r y
-- aux-face-Δ̬ (succ-ℕ (succ-ℕ (succ-ℕ n))) 0 (x , y , u) = x =̬ y ∧̬ Δ̬ (succ-ℕ (succ-ℕ n)) (y , u)
-- aux-face-Δ̬ (succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (x , y , u) = x ≥̬ y ∧̬ aux-face-Δ̬ (succ-ℕ (succ-ℕ n)) r (y , u)

-- first-face-Δ̬ : (n : ℕ) → Shape (simplicial-cube n)
-- first-face-Δ̬ 0 _ = ⊥ᵥ
-- first-face-Δ̬ 1 x = 1₂ =̬ x
-- first-face-Δ̬ 2 (x , _) = 1₂ =̬ x
-- first-face-Δ̬ (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , u) = 1₂ =̬ x ∧̬ Δ̬ (succ-ℕ (succ-ℕ n)) u

-- face-Δ̬ : (n r : ℕ) → Shape (simplicial-cube n)
-- face-Δ̬ n 0 = first-face-Δ̬ n
-- face-Δ̬ n (succ-ℕ r) = aux-face-Δ̬ n r
-- -- These definitions would be a bit simpler if we used list induction

-- faces-up-to-Δ̬ : (n k : ℕ) → Shape (simplicial-cube n)
-- faces-up-to-Δ̬ n 0 = face-Δ̬ n 0
-- faces-up-to-Δ̬ n (succ-ℕ k) = face-Δ̬ n (succ-ℕ k) ∪̬ faces-up-to-Δ̬ n k

-- ∂Δ̬ : (n : ℕ) → Shape (simplicial-cube n)
-- ∂Δ̬ n = faces-up-to-Δ̬ n n

-- ∂Δ = Ŝ ∘ ∂Δ̬

-- TODO: add alternative definition
```

### The boundary of the standard simplex is included in the standard simplex

```agda
-- Δ⊇aux-face-Δ : (n r : ℕ) → aux-face-Δ̬ n r ⊆̂ Δ̬ n
-- Δ⊇aux-face-Δ 1 0 _ _ = star
-- Δ⊇aux-face-Δ 2 0 _ = hrefl-≤'
-- Δ⊇aux-face-Δ 2 1 _ = hmin-≤
-- Δ⊇aux-face-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (x=y , d) = hrefl-≤' x=y , d
-- Δ⊇aux-face-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (_ , u) (x≥y , f) =
--   x≥y , Δ⊇aux-face-Δ (succ-ℕ (succ-ℕ n)) r u f

-- Δ⊇face-Δ : (n r : ℕ) → face-Δ̬ n r ⊆̂ Δ̬ n
-- Δ⊇face-Δ 1 0 _ _ = star
-- Δ⊇face-Δ 1 (succ-ℕ r) _ _ = star
-- Δ⊇face-Δ 2 0 _ = hmax-≤'
-- Δ⊇face-Δ 2 (succ-ℕ r) = Δ⊇aux-face-Δ 2 r
-- Δ⊇face-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (1=x , p) = hmax-≤' 1=x , p
-- Δ⊇face-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) = Δ⊇aux-face-Δ (succ-ℕ (succ-ℕ (succ-ℕ n))) r

-- Δ⊇faces-up-to-Δ : (n k : ℕ) → faces-up-to-Δ̬ n k ⊆̂ Δ̬ n
-- Δ⊇faces-up-to-Δ n 0 = Δ⊇face-Δ n 0
-- Δ⊇faces-up-to-Δ n (succ-ℕ k) x =
--   elim-disj-tope
--     ( Δ⊇face-Δ n (succ-ℕ k) x)
--     ( Δ⊇faces-up-to-Δ n k x)

-- Δ⊇∂Δ : (n : ℕ) → ∂Δ̬ n ⊆̂ Δ̬ n
-- Δ⊇∂Δ n = Δ⊇faces-up-to-Δ n n
```

```agda
-- -- face-Δ' : (n r : ℕ) → Shape (simplicial-cube n)
-- -- face-Δ' n 0 = first-face-Δ' n
-- -- face-Δ' n (succ-ℕ r) = aux-face-Δ' n r

-- -- faces-and-up-Δ : (n k : ℕ) → Shape (simplicial-cube n)
-- -- faces-and-up-Δ = {!  !}

-- -- aux-Λ : (n k r : ℕ) → Shape (simplicial-cube n)
-- -- aux-Λ n k 0 = {!   !}
-- -- aux-Λ n k (succ-ℕ r) = {!   !}

-- -- Λ : (n k : ℕ) → Shape (simplicial-cube n)
-- -- Λ n k = aux-Λ n k k
```
