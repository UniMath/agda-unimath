# Composite maps in inverse sequential diagrams

```agda
module foundation.composite-maps-in-inverse-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-inverse-sequential-diagrams
open import foundation.inverse-sequential-diagrams
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Given a ([dependent](foundation.dependent-inverse-sequential-diagrams.md))
[inverse sequential diagram](foundation.inverse-sequential-diagrams.md) `A`, we
can extract the **composite map from `Aₙ₊ᵣ` to `Aₙ`**.

## Definitions

### Composite maps in inverse sequential diagrams

```agda
comp-map-inverse-sequential-diagram :
  {l : Level} (A : inverse-sequential-diagram l) (n r : ℕ) →
  family-inverse-sequential-diagram A (n +ℕ r) →
  family-inverse-sequential-diagram A n
comp-map-inverse-sequential-diagram A n zero-ℕ = id
comp-map-inverse-sequential-diagram A n (succ-ℕ r) =
  comp-map-inverse-sequential-diagram A n r ∘
  map-inverse-sequential-diagram A (n +ℕ r)
```

### Composite maps in dependent inverse sequential diagrams

```agda
comp-map-dependent-inverse-sequential-diagram :
  {l1 l2 : Level} {A : inverse-sequential-diagram l1}
  (B : dependent-inverse-sequential-diagram l2 A)
  (n r : ℕ) (x : family-inverse-sequential-diagram A (n +ℕ r)) →
  family-dependent-inverse-sequential-diagram B (n +ℕ r) x →
  family-dependent-inverse-sequential-diagram B n
    ( comp-map-inverse-sequential-diagram A n r x)
comp-map-dependent-inverse-sequential-diagram B n zero-ℕ x y = y
comp-map-dependent-inverse-sequential-diagram {A = A} B n (succ-ℕ r) x y =
  comp-map-dependent-inverse-sequential-diagram B n r
    ( map-inverse-sequential-diagram A (n +ℕ r) x)
    ( map-dependent-inverse-sequential-diagram B (n +ℕ r) x y)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
