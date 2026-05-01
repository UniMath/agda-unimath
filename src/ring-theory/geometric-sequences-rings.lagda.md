# Geometric sequences in rings

```agda
module ring-theory.geometric-sequences-rings where
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

open import group-theory.arithmetic-sequences-semigroups

open import lists.sequences

open import ring-theory.geometric-sequences-semirings
open import ring-theory.powers-of-elements-rings
open import ring-theory.rings
```

</details>

## Ideas

A
{{#concept "geometric sequence" Disambiguation="in a ring" Agda=geometric-sequence-Ring}}
in a [ring](ring-theory.rings.md) is a
[geometric sequence](ring-theory.geometric-sequences-semirings.md) in the
underlying [semiring](ring-theory.semirings.md).

These are sequences of the form `n ↦ a * rⁿ`, for elements `a`, `r` in the ring.

## Definitions

### Geometric sequences in rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  geometric-sequence-Ring : UU l
  geometric-sequence-Ring =
    geometric-sequence-Semiring (semiring-Ring R)

module _
  {l : Level} (R : Ring l)
  (u : geometric-sequence-Ring R)
  where

  seq-geometric-sequence-Ring : ℕ → type-Ring R
  seq-geometric-sequence-Ring =
    seq-geometric-sequence-Semiring (semiring-Ring R) u

  common-ratio-geometric-sequence-Ring : type-Ring R
  common-ratio-geometric-sequence-Ring =
    common-ratio-geometric-sequence-Semiring (semiring-Ring R) u

  is-common-ratio-geometric-sequence-Ring :
    ( n : ℕ) →
    ( seq-geometric-sequence-Ring (succ-ℕ n)) ＝
    ( mul-Ring
      ( R)
      ( seq-geometric-sequence-Ring n)
      ( common-ratio-geometric-sequence-Ring))
  is-common-ratio-geometric-sequence-Ring =
    is-common-difference-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Ring R)
      ( u)

  initial-term-geometric-sequence-Ring : type-Ring R
  initial-term-geometric-sequence-Ring =
    initial-term-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Ring R)
      ( u)
```

### The standard geometric sequences in a ring

The standard geometric sequence with initial term `a` and common factor `r` is
the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ * r`

```agda
module _
  {l : Level} (R : Ring l) (a r : type-Ring R)
  where

  standard-geometric-sequence-Ring : geometric-sequence-Ring R
  standard-geometric-sequence-Ring =
    standard-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Ring R)
      ( a)
      ( r)

  seq-standard-geometric-sequence-Ring : ℕ → type-Ring R
  seq-standard-geometric-sequence-Ring =
    seq-geometric-sequence-Ring R
      standard-geometric-sequence-Ring
```

### The geometric sequences `n ↦ a * rⁿ`

```agda
module _
  {l : Level} (R : Ring l) (a r : type-Ring R)
  where

  mul-pow-nat-Ring : sequence (type-Ring R)
  mul-pow-nat-Ring = mul-pow-nat-Semiring (semiring-Ring R) a r

  geometric-mul-pow-nat-Ring : geometric-sequence-Ring R
  geometric-mul-pow-nat-Ring =
    geometric-mul-pow-nat-Semiring (semiring-Ring R) a r

  initial-term-mul-pow-nat-Ring : type-Ring R
  initial-term-mul-pow-nat-Ring =
    initial-term-mul-pow-nat-Semiring (semiring-Ring R) a r

  eq-initial-term-mul-pow-nat-Ring :
    initial-term-mul-pow-nat-Ring ＝ a
  eq-initial-term-mul-pow-nat-Ring =
    eq-initial-term-mul-pow-nat-Semiring (semiring-Ring R) a r
```

## Properties

### Any geometric sequence is homotopic to a standard geometric sequence

```agda
module _
  {l : Level} (R : Ring l)
  (u : geometric-sequence-Ring R)
  where

  htpy-seq-standard-geometric-sequence-Ring :
    ( seq-geometric-sequence-Ring R
      ( standard-geometric-sequence-Ring R
        ( initial-term-geometric-sequence-Ring R u)
        ( common-ratio-geometric-sequence-Ring R u))) ~
    ( seq-geometric-sequence-Ring R u)
  htpy-seq-standard-geometric-sequence-Ring =
    htpy-seq-standard-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Ring R)
      ( u)
```

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

```agda
module _
  {l : Level} (R : Ring l) (a r : type-Ring R)
  where

  htpy-mul-pow-standard-geometric-sequence-Ring :
    mul-pow-nat-Ring R a r ~ seq-standard-geometric-sequence-Ring R a r
  htpy-mul-pow-standard-geometric-sequence-Ring =
    htpy-mul-pow-standard-geometric-sequence-Semiring (semiring-Ring R) a r
```

```agda
module _
  {l : Level} (R : Ring l) (u : geometric-sequence-Ring R)
  where

  htpy-mul-pow-geometric-sequence-Ring :
    mul-pow-nat-Ring
      ( R)
      ( initial-term-geometric-sequence-Ring R u)
      ( common-ratio-geometric-sequence-Ring R u) ~
    seq-geometric-sequence-Ring R u
  htpy-mul-pow-geometric-sequence-Ring =
    htpy-mul-pow-geometric-sequence-Semiring (semiring-Ring R) u
```

### Constant sequences are geometric with common ratio one

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  one-is-common-ratio-const-sequence-Ring :
    is-common-difference-sequence-Semigroup
      ( multiplicative-semigroup-Ring R)
      ( λ _ → a)
      ( one-Ring R)
  one-is-common-ratio-const-sequence-Ring n =
    inv (right-unit-law-mul-Ring R a)

  geometric-const-sequence-Ring : geometric-sequence-Ring R
  geometric-const-sequence-Ring =
    geometric-const-sequence-Semiring (semiring-Ring R) a
```

## See also

- [Geometric sequences in a semiring](ring-theory.geometric-sequences-semirings.md)

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
