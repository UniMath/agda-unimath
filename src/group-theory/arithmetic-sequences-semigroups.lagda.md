# Arithmetic sequences in semigroups

```agda
module group-theory.arithmetic-sequences-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.semigroups

open import lists.sequences
```

</details>

## Ideas

A [sequence](lists.sequences.md) `u` in a
[semigroup](group-theory.semigroups.md) `G` is called
{{#concept "arithmetic" Disambiguation="sequence in a semigroup" Agda=arithmetic-sequence-Semigroup WD="arithmetic progression" WDID=Q170008}}
with common difference `d : type-Semigroup G` if the successor term of `u` is
obtained by adding `d` in `G`: `∀ (n : ℕ), uₙ₊₁ = uₙ + d`.

## Definitions

### Sequences in a semigroup with a common difference

```agda
module _
  {l : Level} (G : Semigroup l) (u : ℕ → type-Semigroup G)
  where

  is-difference-term-prop-sequence-Semigroup : type-Semigroup G → ℕ → Prop l
  is-difference-term-prop-sequence-Semigroup d n =
    Id-Prop (set-Semigroup G) (u (succ-ℕ n)) (mul-Semigroup G (u n) d)

  is-difference-term-sequence-Semigroup : type-Semigroup G → ℕ → UU l
  is-difference-term-sequence-Semigroup d n =
    type-Prop (is-difference-term-prop-sequence-Semigroup d n)

  is-common-difference-prop-sequence-Semigroup : type-Semigroup G → Prop l
  is-common-difference-prop-sequence-Semigroup d =
    Π-Prop ℕ (is-difference-term-prop-sequence-Semigroup d)

  is-common-difference-sequence-Semigroup : type-Semigroup G → UU l
  is-common-difference-sequence-Semigroup d =
    type-Prop (is-common-difference-prop-sequence-Semigroup d)

  is-arithmetic-sequence-Semigroup : UU l
  is-arithmetic-sequence-Semigroup =
    Σ (type-Semigroup G) (is-common-difference-sequence-Semigroup)
```

### Arithmetic sequences in a semigroup

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  arithmetic-sequence-Semigroup : UU l
  arithmetic-sequence-Semigroup =
    Σ (ℕ → type-Semigroup G) (is-arithmetic-sequence-Semigroup G)

module _
  {l : Level} (G : Semigroup l) (u : arithmetic-sequence-Semigroup G)
  where

  seq-arithmetic-sequence-Semigroup : ℕ → type-Semigroup G
  seq-arithmetic-sequence-Semigroup = pr1 u

  is-arithmetic-seq-arithmetic-sequence-Semigroup :
    is-arithmetic-sequence-Semigroup G seq-arithmetic-sequence-Semigroup
  is-arithmetic-seq-arithmetic-sequence-Semigroup = pr2 u

  common-difference-arithmetic-sequence-Semigroup : type-Semigroup G
  common-difference-arithmetic-sequence-Semigroup =
    pr1 is-arithmetic-seq-arithmetic-sequence-Semigroup

  is-common-difference-arithmetic-sequence-Semigroup :
    is-common-difference-sequence-Semigroup G
      seq-arithmetic-sequence-Semigroup
      common-difference-arithmetic-sequence-Semigroup
  is-common-difference-arithmetic-sequence-Semigroup =
    pr2 is-arithmetic-seq-arithmetic-sequence-Semigroup

  initial-term-arithmetic-sequence-Semigroup : type-Semigroup G
  initial-term-arithmetic-sequence-Semigroup =
    seq-arithmetic-sequence-Semigroup zero-ℕ
```

### The standard arithmetic sequence in a semigroup

The standard arithmetic sequence with initial term `a` and common difference `d`
is the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ + d`

```agda
module _
  {l : Level} (G : Semigroup l) (a d : type-Semigroup G)
  where

  seq-standard-arithmetic-sequence-Semigroup : sequence (type-Semigroup G)
  seq-standard-arithmetic-sequence-Semigroup zero-ℕ = a
  seq-standard-arithmetic-sequence-Semigroup (succ-ℕ n) =
    mul-Semigroup G
      ( seq-standard-arithmetic-sequence-Semigroup n)
      ( d)

  is-arithmetic-sequence-standard-arithmetic-sequence-Semigroup :
    is-arithmetic-sequence-Semigroup G
      seq-standard-arithmetic-sequence-Semigroup
  is-arithmetic-sequence-standard-arithmetic-sequence-Semigroup = d , λ n → refl

  standard-arithmetic-sequence-Semigroup : arithmetic-sequence-Semigroup G
  standard-arithmetic-sequence-Semigroup =
    seq-standard-arithmetic-sequence-Semigroup ,
    is-arithmetic-sequence-standard-arithmetic-sequence-Semigroup
```

## Properties

### Two arithmetic sequences in a semigroup with the same initial term and the same common difference are homotopic

```agda
module _
  { l : Level} (G : Semigroup l)
  ( u v : arithmetic-sequence-Semigroup G)
  ( eq-init :
    initial-term-arithmetic-sequence-Semigroup G u ＝
    initial-term-arithmetic-sequence-Semigroup G v)
  ( eq-common-difference :
    common-difference-arithmetic-sequence-Semigroup G u ＝
    common-difference-arithmetic-sequence-Semigroup G v)
  where

  htpy-seq-arithmetic-sequence-Semigroup :
    seq-arithmetic-sequence-Semigroup G u ~
    seq-arithmetic-sequence-Semigroup G v
  htpy-seq-arithmetic-sequence-Semigroup zero-ℕ = eq-init
  htpy-seq-arithmetic-sequence-Semigroup (succ-ℕ n) =
    binary-tr
      ( Id)
      ( inv (is-common-difference-arithmetic-sequence-Semigroup G u n))
      ( inv (is-common-difference-arithmetic-sequence-Semigroup G v n))
      ( ap-binary
        ( mul-Semigroup G)
        ( htpy-seq-arithmetic-sequence-Semigroup n)
        ( eq-common-difference))
```

### Any arithmetic sequence in a semigroup is homotopic to a standard arithmetic sequence

```agda
module _
  {l : Level} (G : Semigroup l)
  (u : arithmetic-sequence-Semigroup G)
  where

  htpy-seq-standard-arithmetic-sequence-Semigroup :
    ( seq-arithmetic-sequence-Semigroup G
      ( standard-arithmetic-sequence-Semigroup G
        ( initial-term-arithmetic-sequence-Semigroup G u)
        ( common-difference-arithmetic-sequence-Semigroup G u))) ~
    ( seq-arithmetic-sequence-Semigroup G u)
  htpy-seq-standard-arithmetic-sequence-Semigroup =
    htpy-seq-arithmetic-sequence-Semigroup G
      ( standard-arithmetic-sequence-Semigroup G
        ( initial-term-arithmetic-sequence-Semigroup G u)
        ( common-difference-arithmetic-sequence-Semigroup G u))
      ( u)
      ( refl)
      ( refl)
```

## External links

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
