# Cones over towers

```agda
module foundation.cones-over-towers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers-of-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **cone** on a [tower](foundation.towers-of-types.md) `A` with domain `X` is a
[sequence](foundation.dependent-sequences.md) of functions from `X` into the
sequence of types of `A` such that the triangles

```text
     X
    / \
   /   \
  v     v
 Aₙ₊₁ -> Aₙ
```

commute for all `n : ℕ`.

## Definitions

### Cones on towers

```agda
module _
  {l1 : Level} (A : Tower l1)
  where

  cone-Tower : {l2 : Level} → UU l2 → UU (l1 ⊔ l2)
  cone-Tower X =
    Σ ( (n : ℕ) → X → type-Tower A n)
      ( λ f →
        (n : ℕ) → coherence-triangle-maps (f n) (map-Tower A n) (f (succ-ℕ n)))

  map-cone-Tower :
    {l2 : Level} {X : UU l2} → cone-Tower X → (n : ℕ) → X → type-Tower A n
  map-cone-Tower = pr1

  coherence-cone-Tower :
    {l2 : Level} {X : UU l2} (c : cone-Tower X) (n : ℕ) →
    coherence-triangle-maps
      ( map-cone-Tower c n)
      ( map-Tower A n)
      ( map-cone-Tower c (succ-ℕ n))
  coherence-cone-Tower = pr2
```
