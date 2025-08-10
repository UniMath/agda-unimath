# Geomeric sequences in semirings

```agda
module ring-theory.geometric-sequences-semirings where
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
open import foundation.sequences
open import foundation.sets
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups

open import ring-theory.powers-of-elements-semirings
open import ring-theory.semirings
```

</details>

## Ideas

An
{{#concept "geometric sequence" Disambiguation="in a semiring" Agda=geometric-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is an
[arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in the
semiring multiplicative [semigroup](group-theory.semigroups.md).

These are the sequences `n ↦ a * r ⁿ` for some elements `a r` in the semiring.

## Definitions

### Geometric sequences in semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  geometric-sequence-Semiring : UU l
  geometric-sequence-Semiring =
    arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)

module _
  {l : Level} (R : Semiring l)
  (u : geometric-sequence-Semiring R)
  where

  seq-geometric-sequence-Semiring : ℕ → type-Semiring R
  seq-geometric-sequence-Semiring =
    seq-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)

  is-geometric-seq-geometric-sequence-Semiring :
    is-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( seq-geometric-sequence-Semiring)
  is-geometric-seq-geometric-sequence-Semiring =
    is-arithmetic-seq-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)

  common-ratio-geometric-sequence-Semiring : type-Semiring R
  common-ratio-geometric-sequence-Semiring =
    common-difference-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)

  is-common-ratio-geometric-sequence-Semiring :
    ( n : ℕ) →
    ( seq-geometric-sequence-Semiring (succ-ℕ n)) ＝
    ( mul-Semiring
      ( R)
      ( seq-geometric-sequence-Semiring n)
      ( common-ratio-geometric-sequence-Semiring))
  is-common-ratio-geometric-sequence-Semiring =
    is-common-difference-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)

  initial-term-geometric-sequence-Semiring : type-Semiring R
  initial-term-geometric-sequence-Semiring =
    initial-term-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)
```

### The standard geometric sequences in a semiring

The standard geometric sequence with initial term `a` and common factor `r` is
the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ * r`

```agda
module _
  {l : Level} (R : Semiring l) (a r : type-Semiring R)
  where

  standard-geometric-sequence-Semiring : geometric-sequence-Semiring R
  standard-geometric-sequence-Semiring =
    standard-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( a)
      ( r)

  seq-standard-geometric-sequence-Semiring : ℕ → type-Semiring R
  seq-standard-geometric-sequence-Semiring =
    seq-geometric-sequence-Semiring R
      standard-geometric-sequence-Semiring

  is-geometric-standard-geometric-sequence-Semiring :
    is-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( seq-standard-geometric-sequence-Semiring)
  is-geometric-standard-geometric-sequence-Semiring =
    is-geometric-seq-geometric-sequence-Semiring R
      standard-geometric-sequence-Semiring
```

### The geometric sequences `n ↦ a * r ⁿ`

```agda
module _
  {l : Level} (R : Semiring l) (a r : type-Semiring R)
  where

  mul-pow-nat-Semiring : ℕ → type-Semiring R
  mul-pow-nat-Semiring n =
    mul-Semiring R a (power-Semiring R n r)

  common-ratio-mul-pow-nat-Semiring :
    is-common-difference-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( mul-pow-nat-Semiring)
      ( r)
  common-ratio-mul-pow-nat-Semiring n =
    ( ap
      ( mul-Semiring R a)
      ( power-succ-Semiring R n r)) ∙
    ( inv
      ( associative-mul-Semiring
        ( R)
        ( a)
        ( power-Semiring R n r)
        ( r)))

  is-geometric-mul-pow-nat-Semiring :
    is-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( mul-pow-nat-Semiring)
  is-geometric-mul-pow-nat-Semiring =
    ( r , common-ratio-mul-pow-nat-Semiring)

  geometric-mul-pow-nat-Semiring : geometric-sequence-Semiring R
  geometric-mul-pow-nat-Semiring =
    ( mul-pow-nat-Semiring , is-geometric-mul-pow-nat-Semiring)

  initial-term-mul-pow-nat-Semiring : type-Semiring R
  initial-term-mul-pow-nat-Semiring =
    initial-term-geometric-sequence-Semiring
      ( R)
      ( geometric-mul-pow-nat-Semiring)

  eq-initial-term-mul-pow-nat-Semiring :
    initial-term-mul-pow-nat-Semiring ＝ a
  eq-initial-term-mul-pow-nat-Semiring =
    right-unit-law-mul-Semiring R a
```

## Properties

### Any geometric sequence in a semiring is homotopic to a standard geometric sequence

```agda
module _
  {l : Level} (R : Semiring l)
  (u : geometric-sequence-Semiring R)
  where

  htpy-seq-standard-geometric-sequence-Semiring :
    ( seq-geometric-sequence-Semiring R
      ( standard-geometric-sequence-Semiring R
        ( initial-term-geometric-sequence-Semiring R u)
        ( common-ratio-geometric-sequence-Semiring R u))) ~
    ( seq-geometric-sequence-Semiring R u)
  htpy-seq-standard-geometric-sequence-Semiring =
    htpy-seq-standard-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)
```

### The nth term of an geometric sequence with initial term `a` and common ratio `r` is `a * r ⁿ`

```agda
module _
  {l : Level} (R : Semiring l) (a r : type-Semiring R)
  where

  htpy-mul-pow-standard-geometric-sequence-Semiring :
    mul-pow-nat-Semiring R a r ~ seq-standard-geometric-sequence-Semiring R a r
  htpy-mul-pow-standard-geometric-sequence-Semiring =
    htpy-seq-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( geometric-mul-pow-nat-Semiring R a r)
      ( standard-geometric-sequence-Semiring R a r)
      ( eq-initial-term-mul-pow-nat-Semiring R a r)
      ( refl)
```

```agda
module _
  {l : Level} (R : Semiring l) (u : geometric-sequence-Semiring R)
  where

  htpy-mul-pow-geometric-sequence-Semiring :
    mul-pow-nat-Semiring
      ( R)
      ( initial-term-geometric-sequence-Semiring R u)
      ( common-ratio-geometric-sequence-Semiring R u) ~
    seq-geometric-sequence-Semiring R u
  htpy-mul-pow-geometric-sequence-Semiring n =
    ( htpy-mul-pow-standard-geometric-sequence-Semiring
      ( R)
      ( initial-term-geometric-sequence-Semiring R u)
      ( common-ratio-geometric-sequence-Semiring R u)
      ( n)) ∙
    ( htpy-seq-standard-arithmetic-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( u)
      ( n))
```

### Constant sequences are gemoetric with common ratio one

```agda
module _
  {l : Level} (R : Semiring l) (a : type-Semiring R)
  where

  one-common-ratio-const-sequence-Semiring :
    is-common-difference-sequence-Semigroup
      ( multiplicative-semigroup-Semiring R)
      ( λ _ → a)
      ( one-Semiring R)
  one-common-ratio-const-sequence-Semiring n =
    inv (right-unit-law-mul-Semiring R a)

  geometric-const-sequence-Semiring : geometric-sequence-Semiring R
  pr1 geometric-const-sequence-Semiring _ = a
  pr2 geometric-const-sequence-Semiring =
    ( one-Semiring R , one-common-ratio-const-sequence-Semiring)
```

## External links

- [Geometric progressions](https://en.wikipedia.org/wiki/Geometric_progression)
  at Wikipedia
