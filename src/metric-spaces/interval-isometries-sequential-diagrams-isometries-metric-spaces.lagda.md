# Interval isometries of sequential diagrams of isometries between metric spaces

```agda
module metric-spaces.interval-isometries-sequential-diagrams-isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cocones-sequential-diagrams-isometries-metric-spaces
open import metric-spaces.indexed-sums-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.sequential-diagrams-isometries-metric-spaces
open import metric-spaces.shifts-sequential-diagrams-isometries-metric-spaces

open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

Let `(M , f)` be a
[sequential diagram](metric-spaces.sequential-diagrams-isometries-metric-spaces.md)
of [isometries](metric-spaces.isometries-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md):

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯
```

The family of
{{#concept "interval isometries" Agda=isometry-leq-sequential-diagram-isometry-Metric-Space}}
indexed by ordered pairs of
[natural numbers](elementary-number-theory.natural-numbers.md) is defined for
`i j : ℕ` with `i ≤ j` as the compositon of isometries:

```text
            fᵢ          fᵢ₊₁                 Mⱼ₋₁
  ϕᵢʲ : Mᵢ ----> Mᵢ₊₁ -------> Mᵢ₊₂ --> ... ------> Mⱼ.
```

It satisfies:

- for any `i : ℕ`, `ϕᵢⁱ ~ id`;
- for any `i j k : ℕ` with `i ≤ j` and `j ≤ k`, `ϕᵢᵏ ~ ϕⱼᵏ ∘ ϕᵢʲ`.

## Definitions

### Induced isometries by intervals of natural numbers

If `(M , f) : M₀ → M₁ → M₂ → ...` is a sequential diagram of isometries, then
for any `i j : ℕ` with `i ≤ j`, there's an isometry `Mᵢ → Mⱼ` obtained by
composition of the `fₙ`s.

```agda
module _
  {l1 l2 : Level}
  where

  isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    leq-ℕ i j →
    isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ H =
    id-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) H =
      comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( j)
          ( H))
  isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) H =
    isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( H)

  map-isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    leq-ℕ i j →
    family-sequential-diagram-isometry-Metric-Space M i →
    family-sequential-diagram-isometry-Metric-Space M j
  map-isometry-leq-sequential-diagram-isometry-Metric-Space M i j H =
    map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j H)
```

## Properties

### Identity law

The interval isometry of a singleton interval is the identity:

```text
  ∀ (i : ℕ) → ϕᵢⁱ ~ id
```

```agda
module _
  {l1 l2 : Level}
  where

  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (n : ℕ) →
    (H : leq-ℕ n n) →
    map-isometry-leq-sequential-diagram-isometry-Metric-Space M n n H ~ id
  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ H = refl-htpy
  compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ n) H =
    compute-map-isometry-diag-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( n)
      ( H)
```

### Successor law

```text
  ∀ (i : ℕ) → ϕᵢⁱ⁺¹ ~ fᵢ
```

```agda
module _
  {l1 l2 : Level}
  where

  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (n : ℕ) →
    (H : leq-ℕ n (succ-ℕ n)) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M n)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ n))
      ( isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( n)
        ( succ-ℕ n)
        ( H))
      ( seq-isometry-sequential-diagram-isometry-Metric-Space M n)
  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ H = refl-htpy
  compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ n) H =
    compute-map-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( n)
      ( H)
```

### Coherence law

For any `i j : ℕ` with `i ≤ j`, there's a commuting square of isometries

```text
        fᵢ
  Mᵢ ------> Mᵢ₊₁
  |           |
  |           |
  |           |
  v           v
  Mⱼ ------> Mⱼ₊₁
        fⱼ
```

```agda
module _
  {l1 l2 : Level}
  where

  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (i j : ℕ) →
    (H : leq-ℕ i j) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M (succ-ℕ j))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j H))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ i))
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( shift-sequential-diagram-isometry-Metric-Space M)
          ( i)
          ( j)
          ( H))
        ( seq-isometry-sequential-diagram-isometry-Metric-Space M i))
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ H = refl-htpy
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) H x =
      ap
        ( seq-map-isometry-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( j)
          ( H)
          ( x))
  coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) H =
    coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( H)
```

### Composition laws

- For all `i j : ℕ` with `i ≤ j`, `ϕ₀ʲ ~ ϕᵢʲ ∘ ϕ₀ⁱ`;
- for all `i j k : ℕ` with `i ≤ j ≤ k`, `ϕᵢᵏ ~ ϕⱼᵏ ∘ ϕᵢʲ`.

```agda
module _
  {l1 l2 : Level}
  where

  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2)
    (i j : ℕ) →
    (Hi : leq-ℕ zero-ℕ i) →
    (Hj : leq-ℕ zero-ℕ j) →
    (Hij : leq-ℕ i j) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space M zero-ℕ j Hj)
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M zero-ℕ)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j Hij)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M zero-ℕ i Hi))
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ zero-ℕ Hi Hj Hij = refl-htpy
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ (succ-ℕ j) Hi Hj Hij = refl-htpy
  compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) Hi Hj Hij x =
    coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
      ( M)
      ( zero-ℕ)
      ( j)
      ( Hj)
      ( x) ∙
    compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( Hi)
      ( Hj)
      ( Hij)
      ( seq-map-isometry-sequential-diagram-isometry-Metric-Space M zero-ℕ x) ∙
    ap
      ( map-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          (succ-ℕ i))
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space
          ( M)
          ( succ-ℕ j))
        ( isometry-leq-sequential-diagram-isometry-Metric-Space
          ( shift-sequential-diagram-isometry-Metric-Space M)
          ( i)
          ( j)
          ( Hij)))
      ( inv
        ( coh-square-isometry-succ-leq-sequential-diagram-isometry-Metric-Space
          ( M)
          ( zero-ℕ)
          ( i)
          ( Hi)
          ( x)))

  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space :
    ( M : sequential-diagram-isometry-Metric-Space l1 l2) →
    ( i j k : ℕ) →
    ( Hij : leq-ℕ i j) →
    ( Hjk : leq-ℕ j k) →
    ( Hik : leq-ℕ i k) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
      ( isometry-leq-sequential-diagram-isometry-Metric-Space
        ( M)
        ( i)
        ( k)
        ( Hik))
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M k)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M j k Hjk)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j Hij))
  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
    M zero-ℕ j k Hij Hjk Hik =
    compute-comp-zero-map-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( M)
      ( j)
      ( k)
      ( Hij)
      ( Hik)
      ( Hjk)
  compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
    M (succ-ℕ i) (succ-ℕ j) (succ-ℕ k) Hij Hjk Hik =
    compute-comp-isometry-leq-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( i)
      ( j)
      ( k)
      ( Hij)
      ( Hjk)
      ( Hik)
```

### Cocone laws

For any cocone

```text
     f₀       f₁       f₂
 M₀ ----> M₁ ----> M₂ ----> ⋯ ----> X
```

under a sequential diagram `(M , f)`, the interval isometries `ϕᵢʲ : Mᵢ → Mⱼ`
induce commutative triangles of isometries:

```text
      ϕᵢʲ
 Mᵢ ------> Mⱼ
   \       /
    \     /
  iᵢ \   / iⱼ
      ∨ ∨
       X
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space :
    (M : sequential-diagram-isometry-Metric-Space l1 l2) →
    (X : Metric-Space l3 l4) →
    (C : cocone-sequential-diagram-isometry-Metric-Space M X) →
    (i j : ℕ) →
    (H : leq-ℕ i j) →
    htpy-map-isometry-Metric-Space
      ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
      ( X)
      ( seq-isometry-cocone-sequential-diagram-isometry-Metric-Space M X C i)
      ( comp-isometry-Metric-Space
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M i)
        ( seq-metric-space-sequential-diagram-isometry-Metric-Space M j)
        ( X)
        ( seq-isometry-cocone-sequential-diagram-isometry-Metric-Space M X C j)
        ( isometry-leq-sequential-diagram-isometry-Metric-Space M i j H))
  coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space
    M X C zero-ℕ zero-ℕ H x = refl
  coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space
    M X C zero-ℕ (succ-ℕ j) H x =
    coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space
      ( M)
      ( X)
      ( C)
      ( zero-ℕ)
      ( j)
      ( H)
      ( x) ∙
    coh-triangle-cocone-sequential-diagram-isometry-Metric-Space M X C j _
  coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space
    M X C (succ-ℕ i) (succ-ℕ j) H x =
    coh-triangle-isometry-leq-cocone-shift-sequential-diagram-isometry-Metric-Space
      ( shift-sequential-diagram-isometry-Metric-Space M)
      ( X)
      ( cocone-shift-sequential-diagram-isometry-Metric-Space M X C)
      ( i)
      ( j)
      ( H)
      ( x)
```
