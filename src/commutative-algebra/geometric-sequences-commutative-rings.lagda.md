# Geometric sequences in commutative rings

```agda
module commutative-algebra.geometric-sequences-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.geometric-sequences-commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups

open import lists.finite-sequences
open import lists.sequences
```

</details>

## Ideas

A
{{#concept "geometric sequence" Disambiguation="in a commutative ring" Agda=geometric-sequence-Commutative-Ring}}
in a [commutative ring](ring-theory.commutative-rings.md) is an
[geometric sequence](ring-theory.geometric-sequences-semirings.md) in the
ring's multiplicative [semigroup](group-theory.semigroups.md).

These are sequences of the form `n ↦ a * rⁿ`, for elements `a`, `r` in the
ring.

## Definitions

### Geometric sequences in commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  geometric-sequence-Commutative-Ring : UU l
  geometric-sequence-Commutative-Ring =
    geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  is-geometric-sequence-Commutative-Ring :
    sequence (type-Commutative-Ring R) → UU l
  is-geometric-sequence-Commutative-Ring =
    is-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

module _
  {l : Level} (R : Commutative-Ring l)
  (u : geometric-sequence-Commutative-Ring R)
  where

  seq-geometric-sequence-Commutative-Ring : ℕ → type-Commutative-Ring R
  seq-geometric-sequence-Commutative-Ring =
    seq-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)

  is-geometric-seq-geometric-sequence-Commutative-Ring :
    is-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( seq-geometric-sequence-Commutative-Ring)
  is-geometric-seq-geometric-sequence-Commutative-Ring =
    is-geometric-seq-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)

  common-ratio-geometric-sequence-Commutative-Ring :
    type-Commutative-Ring R
  common-ratio-geometric-sequence-Commutative-Ring =
    common-ratio-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)

  is-common-ratio-geometric-sequence-Commutative-Ring :
    ( n : ℕ) →
    ( seq-geometric-sequence-Commutative-Ring (succ-ℕ n)) ＝
    ( mul-Commutative-Ring
      ( R)
      ( seq-geometric-sequence-Commutative-Ring n)
      ( common-ratio-geometric-sequence-Commutative-Ring))
  is-common-ratio-geometric-sequence-Commutative-Ring =
    is-common-ratio-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)

  initial-term-geometric-sequence-Commutative-Ring :
    type-Commutative-Ring R
  initial-term-geometric-sequence-Commutative-Ring =
    initial-term-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)
```

### The standard geometric sequences in a commutative ring

The standard geometric sequence with initial term `a` and common factor `r` is
the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ * r`

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a r : type-Commutative-Ring R)
  where

  standard-geometric-sequence-Commutative-Ring :
    geometric-sequence-Commutative-Ring R
  standard-geometric-sequence-Commutative-Ring =
    standard-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( a)
      ( r)

  seq-standard-geometric-sequence-Commutative-Ring :
    ℕ → type-Commutative-Ring R
  seq-standard-geometric-sequence-Commutative-Ring =
    seq-geometric-sequence-Commutative-Ring R
      standard-geometric-sequence-Commutative-Ring

  is-geometric-standard-geometric-sequence-Commutative-Ring :
    is-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( seq-standard-geometric-sequence-Commutative-Ring)
  is-geometric-standard-geometric-sequence-Commutative-Ring =
    is-geometric-seq-geometric-sequence-Commutative-Ring R
      standard-geometric-sequence-Commutative-Ring
```

### The geometric sequences `n ↦ a * rⁿ`

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a r : type-Commutative-Ring R)
  where

  mul-pow-nat-Commutative-Ring : ℕ → type-Commutative-Ring R
  mul-pow-nat-Commutative-Ring n =
    mul-Commutative-Ring R a (power-Commutative-Ring R n r)

  geometric-mul-pow-nat-Commutative-Ring : geometric-sequence-Commutative-Ring R
  geometric-mul-pow-nat-Commutative-Ring =
    geometric-mul-pow-nat-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( a)
      ( r)

  initial-term-mul-pow-nat-Commutative-Ring : type-Commutative-Ring R
  initial-term-mul-pow-nat-Commutative-Ring =
    initial-term-geometric-sequence-Commutative-Ring
      ( R)
      ( geometric-mul-pow-nat-Commutative-Ring)

  eq-initial-term-mul-pow-nat-Commutative-Ring :
    initial-term-mul-pow-nat-Commutative-Ring ＝ a
  eq-initial-term-mul-pow-nat-Commutative-Ring =
    right-unit-law-mul-Commutative-Ring R a
```

## Properties

### Any geometric sequence is homotopic to a standard geometric sequence

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (u : geometric-sequence-Commutative-Ring R)
  where

  htpy-seq-standard-geometric-sequence-Commutative-Ring :
    ( seq-geometric-sequence-Commutative-Ring R
      ( standard-geometric-sequence-Commutative-Ring R
        ( initial-term-geometric-sequence-Commutative-Ring R u)
        ( common-ratio-geometric-sequence-Commutative-Ring R u))) ~
    ( seq-geometric-sequence-Commutative-Ring R u)
  htpy-seq-standard-geometric-sequence-Commutative-Ring =
    htpy-seq-standard-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)
```

### The nth term of a geometric sequence with initial term `a` and common ratio `r` is `a * rⁿ`

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a r : type-Commutative-Ring R)
  where

  htpy-mul-pow-standard-geometric-sequence-Commutative-Ring :
    mul-pow-nat-Commutative-Ring R a r ~
    seq-standard-geometric-sequence-Commutative-Ring R a r
  htpy-mul-pow-standard-geometric-sequence-Commutative-Ring =
    htpy-mul-pow-standard-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( a)
      ( r)

  initial-term-standard-geometric-sequence-Commutative-Ring :
    seq-standard-geometric-sequence-Commutative-Ring R a r 0 ＝ a
  initial-term-standard-geometric-sequence-Commutative-Ring =
    ( inv (htpy-mul-pow-standard-geometric-sequence-Commutative-Ring 0)) ∙
    ( eq-initial-term-mul-pow-nat-Commutative-Ring R a r)
```

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (u : geometric-sequence-Commutative-Ring R)
  where

  htpy-mul-pow-geometric-sequence-Commutative-Ring :
    mul-pow-nat-Commutative-Ring
      ( R)
      ( initial-term-geometric-sequence-Commutative-Ring R u)
      ( common-ratio-geometric-sequence-Commutative-Ring R u) ~
    seq-geometric-sequence-Commutative-Ring R u
  htpy-mul-pow-geometric-sequence-Commutative-Ring n =
    ( htpy-mul-pow-standard-geometric-sequence-Commutative-Ring
      ( R)
      ( initial-term-geometric-sequence-Commutative-Ring R u)
      ( common-ratio-geometric-sequence-Commutative-Ring R u)
      ( n)) ∙
    ( htpy-seq-standard-geometric-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( u)
      ( n))
```

### Constant sequences are geometric with common ratio one

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a : type-Commutative-Ring R)
  where

  geometric-const-sequence-Commutative-Ring :
    geometric-sequence-Commutative-Ring R
  geometric-const-sequence-Commutative-Ring =
    geometric-const-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( a)
```

### Finite geometric sequences

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a r : type-Commutative-Ring R)
  where

  standard-geometric-fin-sequence-Commutative-Ring :
    (n : ℕ) → fin-sequence (type-Commutative-Ring R) n
  standard-geometric-fin-sequence-Commutative-Ring =
    fin-sequence-sequence
      ( seq-standard-geometric-sequence-Commutative-Ring R a r)

  sum-standard-geometric-fin-sequence-Commutative-Ring :
    (n : ℕ) → type-Commutative-Ring R
  sum-standard-geometric-fin-sequence-Commutative-Ring =
    sum-standard-geometric-fin-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( a)
      ( r)
```

### The sum of a finite geometric sequence

```agda
module _
  {l : Level} (R : Commutative-Ring l) (a r : type-Commutative-Ring R)
  where

  abstract
    compute-sum-standard-geometric-fin-sequence-succ-Commutative-Ring :
      (n : ℕ) →
      sum-standard-geometric-fin-sequence-Commutative-Ring R
        ( a)
        ( r)
        ( succ-ℕ n) ＝
      add-Commutative-Ring R
        ( a)
        ( mul-Commutative-Ring R
          ( r)
          ( sum-standard-geometric-fin-sequence-Commutative-Ring R a r n))
    compute-sum-standard-geometric-fin-sequence-succ-Commutative-Ring =
      compute-sum-standard-geometric-fin-sequence-succ-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
        ( a)
        ( r)
```
