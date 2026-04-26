# Arithmetic sequences in semirings

```agda
module ring-theory.arithmetic-sequences-semirings where
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

open import ring-theory.multiples-of-elements-semirings
open import ring-theory.semirings
```

</details>

## Ideas

An
{{#concept "arithmetic sequence" Disambiguation="in a semiring" Agda=arithmetic-sequence-Semiring}}
in a [semiring](ring-theory.semirings.md) is an
[arithmetic sequence](group-theory.arithmetic-sequences-semigroups.md) in the
semiring's additive [semigroup](group-theory.semigroups.md).

These are the sequences `n ↦ a + n * d` for some elements `a d` in the semiring.

## Definitions

### Arithmetic sequences in semirings

```agda
module _
  {l : Level} (R : Semiring l)
  where

  arithmetic-sequence-Semiring : UU l
  arithmetic-sequence-Semiring =
    arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)

module _
  {l : Level} (R : Semiring l)
  (u : arithmetic-sequence-Semiring R)
  where

  seq-arithmetic-sequence-Semiring : ℕ → type-Semiring R
  seq-arithmetic-sequence-Semiring =
    seq-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)

  is-arithmetic-seq-arithmetic-sequence-Semiring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( seq-arithmetic-sequence-Semiring)
  is-arithmetic-seq-arithmetic-sequence-Semiring =
    is-arithmetic-seq-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)

  common-difference-arithmetic-sequence-Semiring : type-Semiring R
  common-difference-arithmetic-sequence-Semiring =
    common-difference-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)

  is-common-difference-arithmetic-sequence-Semiring :
    ( n : ℕ) →
    ( seq-arithmetic-sequence-Semiring (succ-ℕ n)) ＝
    ( add-Semiring
      ( R)
      ( seq-arithmetic-sequence-Semiring n)
      ( common-difference-arithmetic-sequence-Semiring))
  is-common-difference-arithmetic-sequence-Semiring =
    is-common-difference-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)

  initial-term-arithmetic-sequence-Semiring : type-Semiring R
  initial-term-arithmetic-sequence-Semiring =
    initial-term-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)
```

### The standard arithmetic sequences in a semiring

The standard arithmetic sequence with initial term `a` and common difference `d`
is the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ + d`

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  standard-arithmetic-sequence-Semiring : arithmetic-sequence-Semiring R
  standard-arithmetic-sequence-Semiring =
    standard-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( a)
      ( d)

  seq-standard-arithmetic-sequence-Semiring : ℕ → type-Semiring R
  seq-standard-arithmetic-sequence-Semiring =
    seq-arithmetic-sequence-Semiring R
      standard-arithmetic-sequence-Semiring

  is-arithmetic-standard-arithmetic-sequence-Semiring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( seq-standard-arithmetic-sequence-Semiring)
  is-arithmetic-standard-arithmetic-sequence-Semiring =
    is-arithmetic-seq-arithmetic-sequence-Semiring R
      standard-arithmetic-sequence-Semiring
```

### The arithmetic sequences `n ↦ a + n * d`

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  add-mul-nat-Semiring : ℕ → type-Semiring R
  add-mul-nat-Semiring n =
    add-Semiring R a (multiple-Semiring R n d)

  is-common-difference-add-mul-nat-Semiring :
    is-common-difference-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( add-mul-nat-Semiring)
      ( d)

  is-common-difference-add-mul-nat-Semiring n =
    equational-reasoning
      add-Semiring R a (multiple-Semiring R (succ-ℕ n) d)
      ＝ add-Semiring R a (add-Semiring R (multiple-Semiring R n d) d)
        by ap-add-Semiring R refl (multiple-succ-Semiring R n d)
      ＝ add-Semiring R (add-mul-nat-Semiring n) d
        by inv (associative-add-Semiring R _ _ _)

  is-arithmetic-add-mul-nat-Semiring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( add-mul-nat-Semiring)
  is-arithmetic-add-mul-nat-Semiring =
    ( d , is-common-difference-add-mul-nat-Semiring)

  arithmetic-add-mul-nat-Semiring : arithmetic-sequence-Semiring R
  arithmetic-add-mul-nat-Semiring =
    ( add-mul-nat-Semiring , is-arithmetic-add-mul-nat-Semiring)

  initial-term-add-mul-nat-Semiring : type-Semiring R
  initial-term-add-mul-nat-Semiring =
    initial-term-arithmetic-sequence-Semiring
      ( R)
      ( arithmetic-add-mul-nat-Semiring)

  eq-initial-term-add-mul-nat-Semiring :
    initial-term-add-mul-nat-Semiring ＝ a
  eq-initial-term-add-mul-nat-Semiring =
    ( ( ap
        ( add-Semiring R a)
        ( inv (left-zero-law-multiple-Semiring R d))) ∙
    ( right-unit-law-add-Semiring R a))
```

## Properties

### Any arithmetic sequence in a semiring is homotopic to a standard arithmetic sequence

```agda
module _
  {l : Level} (R : Semiring l)
  (u : arithmetic-sequence-Semiring R)
  where

  htpy-seq-standard-arithmetic-sequence-Semiring :
    ( seq-arithmetic-sequence-Semiring R
      ( standard-arithmetic-sequence-Semiring R
        ( initial-term-arithmetic-sequence-Semiring R u)
        ( common-difference-arithmetic-sequence-Semiring R u))) ~
    ( seq-arithmetic-sequence-Semiring R u)
  htpy-seq-standard-arithmetic-sequence-Semiring =
    htpy-seq-standard-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)
```

### The nth term of an arithmetic sequence with initial term `a` and common difference `d` is `a + n * d`

```agda
module _
  {l : Level} (R : Semiring l) (a d : type-Semiring R)
  where

  htpy-add-mul-standard-arithmetic-sequence-Semiring :
    add-mul-nat-Semiring R a d ~ seq-standard-arithmetic-sequence-Semiring R a d
  htpy-add-mul-standard-arithmetic-sequence-Semiring =
    htpy-seq-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( arithmetic-add-mul-nat-Semiring R a d)
      ( standard-arithmetic-sequence-Semiring R a d)
      ( eq-initial-term-add-mul-nat-Semiring R a d)
      ( refl)
```

```agda
module _
  {l : Level} (R : Semiring l) (u : arithmetic-sequence-Semiring R)
  where

  htpy-add-mul-arithmetic-sequence-Semiring :
    add-mul-nat-Semiring
      ( R)
      ( initial-term-arithmetic-sequence-Semiring R u)
      ( common-difference-arithmetic-sequence-Semiring R u) ~
    seq-arithmetic-sequence-Semiring R u
  htpy-add-mul-arithmetic-sequence-Semiring n =
    ( htpy-add-mul-standard-arithmetic-sequence-Semiring
      ( R)
      ( initial-term-arithmetic-sequence-Semiring R u)
      ( common-difference-arithmetic-sequence-Semiring R u)
      ( n)) ∙
    ( htpy-seq-standard-arithmetic-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( u)
      ( n))
```

### Constant sequences are arithmetic with common difference zero

```agda
module _
  {l : Level} (R : Semiring l) (a : type-Semiring R)
  where

  zero-is-common-difference-const-sequence-Semiring :
    is-common-difference-sequence-Semigroup
      ( additive-semigroup-Semiring R)
      ( λ _ → a)
      ( zero-Semiring R)
  zero-is-common-difference-const-sequence-Semiring n =
    inv (right-unit-law-add-Semiring R a)

  arithmetic-const-sequence-Semiring : arithmetic-sequence-Semiring R
  pr1 arithmetic-const-sequence-Semiring _ = a
  pr2 arithmetic-const-sequence-Semiring =
    ( zero-Semiring R , zero-is-common-difference-const-sequence-Semiring)
```

## External links

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
