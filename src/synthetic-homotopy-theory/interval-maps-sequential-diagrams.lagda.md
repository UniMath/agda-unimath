# Interval maps induced by sequential diagrams

```agda
module synthetic-homotopy-theory.interval-maps-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A , a)`, the family of
{{#concept "interval maps" Disambiguation="of sequential diagram" Agda=map-leq-sequential-diagram}}

```text
  ϕᵢʲ : Aᵢ → Aⱼ
```

indexed by pairs `i j : ℕ` with `i ≤ j`, is the family

```text
            aᵢ          aᵢ₊₁                 aⱼ₋₁
  ϕᵢʲ : Aᵢ ----> Aᵢ₊₁ -------> Aᵢ₊₂ --> ... ------> Aⱼ.
```

It satisfies:

- for any `i : ℕ`, `ϕᵢⁱ ~ id`;
- for any `i j k : ℕ` with `i ≤ j` and `j ≤ k`, `ϕᵢᵏ ~ ϕⱼᵏ ∘ ϕᵢʲ`.

## Definitions

_Implementation note_: it might be tempting to define the interval maps via maps
`Aᵢ → Aᵢ₊ₖ` by iteration of the maps `aⱼ` for `j ∈ {i ,..., i + k}`. However,
this definition forces the introduction of
[transport](foundation-core.transport-along-identifications.md) to define and
prove the coherence laws.

This implementation uses
[shifted sequences](synthetic-homotopy-theory.shifts-sequential-diagrams.md),
`σ`, so that the diagrams:

```text
              aᵢ
        Aᵢ ------> Aᵢ₊₁
        |           |
 ϕ(A)ᵢʲ |           | ϕ(σA)ᵢʲ ＝ ϕ(A)ᵢ₊₁ʲ⁺¹
        |           |
        v           v
        Aⱼ ------> Aⱼ₊₁
              aⱼ
```

are coherent by definition; this way, the generic coherence laws follow directly
from the definition.

### Induced maps by intervals `i j : ℕ, i ≤ j`

```agda
module _
  {l : Level}
  where

  map-leq-sequential-diagram :
    (A : sequential-diagram l)
    (i j : ℕ) →
    leq-ℕ i j →
    family-sequential-diagram A i →
    family-sequential-diagram A j
  map-leq-sequential-diagram A zero-ℕ zero-ℕ H = id
  map-leq-sequential-diagram A zero-ℕ (succ-ℕ j) H =
    map-sequential-diagram A j ∘ map-leq-sequential-diagram A zero-ℕ j H
  map-leq-sequential-diagram A (succ-ℕ i) (succ-ℕ j) H =
    map-leq-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( i)
      ( j)
      ( H)
```

## Properties

### Singleton interval maps are the identity

For any `n : ℕ`, `ϕₙⁿ ~ id`.

```agda
module _
  {l : Level}
  where

  compute-map-diag-leq-sequential-diagram :
    (A : sequential-diagram l) →
    (n : ℕ) →
    (H : leq-ℕ n n) →
    map-leq-sequential-diagram A n n H ~ id
  compute-map-diag-leq-sequential-diagram A zero-ℕ H = refl-htpy
  compute-map-diag-leq-sequential-diagram A (succ-ℕ n) H =
    compute-map-diag-leq-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( n)
      ( H)
```

### Coherence laws w.r.t to `(A , a)`

For any `i j : ℕ` with `i ≤ j`, there's a commutative diagram

```text
         aᵢ
     Aᵢ ------> Aᵢ₊₁
     |           |
 ϕᵢʲ |           | Φᵢʲ
     |           |
     v           v
     Aⱼ ------> Aⱼ₊₁
          aⱼ
```

where `Φ` is the interval map in the
[shifted sequence](synthetic-homotopy-theory.shifts-sequential-diagrams.md) of
`A`.

```agda
module _
  {l : Level}
  where

  coh-square-map-leq-shift-sequential-diagram :
    (A : sequential-diagram l) →
    (i j : ℕ) →
    (Hij : leq-ℕ i j) →
    map-sequential-diagram A j ∘
    map-leq-sequential-diagram A i j Hij ~
    map-leq-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( i)
      ( j)
      ( Hij) ∘
    map-sequential-diagram A i
  coh-square-map-leq-shift-sequential-diagram A zero-ℕ zero-ℕ Hij x = refl
  coh-square-map-leq-shift-sequential-diagram A zero-ℕ (succ-ℕ j) Hij x =
    ap
      ( map-sequential-diagram A (succ-ℕ j))
      ( coh-square-map-leq-shift-sequential-diagram A zero-ℕ j Hij x)
  coh-square-map-leq-shift-sequential-diagram A (succ-ℕ i) (succ-ℕ j) Hij x =
    coh-square-map-leq-shift-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( i)
      ( j)
      ( Hij)
      ( x)
```

### Composition law

Let `(A , a)` be a sequential diagram;

- for any `i ≤ j ∈ ℕ`, `ϕ₀j ~ ϕᵢʲ ∘ ϕ₀ⁱ`;
- for any `i ≤ j ≤ k ∈ ℕ`, `ϕᵢᵏ ~ ϕⱼᵏ ∘ ϕᵢʲ`.

```agda
module _
  {l : Level}
  where

  compute-comp-zero-map-leq-sequential-diagram :
    (A : sequential-diagram l) →
    (i j : ℕ) →
    (Hi : leq-ℕ zero-ℕ i) →
    (Hj : leq-ℕ zero-ℕ j) →
    (Hij : leq-ℕ i j) →
    map-leq-sequential-diagram A zero-ℕ j Hj ~
    map-leq-sequential-diagram A i j Hij ∘
    map-leq-sequential-diagram A zero-ℕ i Hi
  compute-comp-zero-map-leq-sequential-diagram
    A zero-ℕ zero-ℕ Hi Hj Hij x = refl
  compute-comp-zero-map-leq-sequential-diagram
    A zero-ℕ (succ-ℕ j) Hi Hj Hij x = refl
  compute-comp-zero-map-leq-sequential-diagram
    A (succ-ℕ i) (succ-ℕ j) Hi Hj Hij x =
    coh-square-map-leq-shift-sequential-diagram A zero-ℕ j Hj x ∙
    compute-comp-zero-map-leq-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( i)
      ( j)
      ( Hi)
      ( Hj)
      ( Hij)
      ( map-sequential-diagram A zero-ℕ x) ∙
    ap
      ( map-leq-sequential-diagram
        ( shift-once-sequential-diagram A)
        ( i)
        ( j)
        ( Hij))
      ( inv
        ( coh-square-map-leq-shift-sequential-diagram A zero-ℕ i Hi x))

  compute-comp-map-leq-sequential-diagram :
    (A : sequential-diagram l) →
    (i j k : ℕ) →
    (Hij : leq-ℕ i j) →
    (Hjk : leq-ℕ j k) →
    (Hik : leq-ℕ i k) →
    map-leq-sequential-diagram A i k Hik ~
    map-leq-sequential-diagram A j k Hjk ∘
    map-leq-sequential-diagram A i j Hij
  compute-comp-map-leq-sequential-diagram
    A zero-ℕ j k Hij Hjk Hik =
    compute-comp-zero-map-leq-sequential-diagram
      ( A)
      ( j)
      ( k)
      ( Hij)
      ( Hik)
      ( Hjk)
  compute-comp-map-leq-sequential-diagram
    A (succ-ℕ i) (succ-ℕ j) (succ-ℕ k) Hij Hjk Hik =
    compute-comp-map-leq-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( i)
      ( j)
      ( k)
      ( Hij)
      ( Hjk)
      ( Hik)
```
