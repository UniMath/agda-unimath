# Arithmetic sequences in rings

```agda
module ring-theory.arithmetic-sequences-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.arithmetic-sequences-semigroups
open import group-theory.function-abelian-groups
open import group-theory.subgroups
open import group-theory.subgroups-abelian-groups

open import ring-theory.arithmetic-sequences-semirings
open import ring-theory.function-rings
open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Ideas

An
{{#concept "arithmetic sequence" Disambiguation="in a ring" Agda=arithmetic-sequence-Ring}}
in a [ring](ring-theory.rings.md) is an
[arithmetic sequence](ring-theory.arithmetic-sequences-semirings.md) in its
underlying [semiring](ring-theory.semirings.md).

These are the sequences `n ↦ a + n * d` for some elements `a d` in the ring.

## Definitions

### Arithmetic sequences in rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-arithmetic-sequence-Ring : (ℕ → type-Ring R) → UU l
  is-arithmetic-sequence-Ring =
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)

  arithmetic-sequence-Ring : UU l
  arithmetic-sequence-Ring =
    arithmetic-sequence-Semiring (semiring-Ring R)

module _
  {l : Level} (R : Ring l)
  (u : arithmetic-sequence-Ring R)
  where

  seq-arithmetic-sequence-Ring : ℕ → type-Ring R
  seq-arithmetic-sequence-Ring =
    seq-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)

  is-arithmetic-seq-arithmetic-sequence-Ring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( seq-arithmetic-sequence-Ring)
  is-arithmetic-seq-arithmetic-sequence-Ring =
    is-arithmetic-seq-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)

  common-difference-arithmetic-sequence-Ring : type-Ring R
  common-difference-arithmetic-sequence-Ring =
    common-difference-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)

  is-common-difference-arithmetic-sequence-Ring :
    ( n : ℕ) →
    ( seq-arithmetic-sequence-Ring (succ-ℕ n)) ＝
    ( add-Ring
      ( R)
      ( seq-arithmetic-sequence-Ring n)
      ( common-difference-arithmetic-sequence-Ring))
  is-common-difference-arithmetic-sequence-Ring =
    is-common-difference-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)

  initial-term-arithmetic-sequence-Ring : type-Ring R
  initial-term-arithmetic-sequence-Ring =
    initial-term-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)

  compute-common-difference-arithmetic-sequence-Ring :
    add-Ring
      ( R)
      ( seq-arithmetic-sequence-Ring 1)
      ( neg-Ring
        ( R)
        ( seq-arithmetic-sequence-Ring 0)) ＝
    common-difference-arithmetic-sequence-Ring
  compute-common-difference-arithmetic-sequence-Ring =
    ( ap
      ( add-Ring' R
        ( neg-Ring R (seq-arithmetic-sequence-Ring 0)))
      ( is-common-difference-arithmetic-sequence-Ring 0 ∙
        commutative-add-Ring R
          ( seq-arithmetic-sequence-Ring 0)
          ( common-difference-arithmetic-sequence-Ring))) ∙
    ( associative-add-Ring R
      ( common-difference-arithmetic-sequence-Ring)
      ( seq-arithmetic-sequence-Ring 0)
      ( neg-Ring R (seq-arithmetic-sequence-Ring 0))) ∙
    ( ap
      ( add-Ring R common-difference-arithmetic-sequence-Ring)
      ( right-inverse-law-add-Ring R (seq-arithmetic-sequence-Ring 0))) ∙
    ( right-unit-law-add-Ring R common-difference-arithmetic-sequence-Ring)
```

### The standard arithmetic sequences in a semiring

The standard arithmetic sequence with initial term `a` and common difference `d`
is the sequence `u` defined by:

- `u₀ = a`
- `uₙ₊₁ = uₙ + d`

```agda
module _
  {l : Level} (R : Ring l) (a d : type-Ring R)
  where

  standard-arithmetic-sequence-Ring : arithmetic-sequence-Ring R
  standard-arithmetic-sequence-Ring =
    standard-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( a)
      ( d)

  seq-standard-arithmetic-sequence-Ring : ℕ → type-Ring R
  seq-standard-arithmetic-sequence-Ring =
    seq-arithmetic-sequence-Ring R
      standard-arithmetic-sequence-Ring

  is-arithmetic-standard-arithmetic-sequence-Ring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( seq-standard-arithmetic-sequence-Ring)
  is-arithmetic-standard-arithmetic-sequence-Ring =
    is-arithmetic-seq-arithmetic-sequence-Ring R
      standard-arithmetic-sequence-Ring
```

### The arithmetic sequences `n ↦ a + n * d`

```agda
module _
  {l : Level} (R : Ring l) (a d : type-Ring R)
  where

  add-mul-nat-Ring : ℕ → type-Ring R
  add-mul-nat-Ring n =
    add-Ring R a (mul-nat-scalar-Ring R n d)

  is-common-difference-add-mul-nat-Ring :
    is-common-difference-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( add-mul-nat-Ring)
      ( d)
  is-common-difference-add-mul-nat-Ring n =
    is-common-difference-add-mul-nat-Semiring
      ( semiring-Ring R)
      ( a)
      ( d)
      ( n)

  is-arithmetic-add-mul-nat-Ring :
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( add-mul-nat-Ring)
  is-arithmetic-add-mul-nat-Ring =
    ( d , is-common-difference-add-mul-nat-Ring)

  arithmetic-add-mul-nat-Ring : arithmetic-sequence-Ring R
  arithmetic-add-mul-nat-Ring =
    ( add-mul-nat-Ring , is-arithmetic-add-mul-nat-Ring)

  initial-term-add-mul-nat-Ring : type-Ring R
  initial-term-add-mul-nat-Ring =
    initial-term-arithmetic-sequence-Ring
      ( R)
      ( arithmetic-add-mul-nat-Ring)

  eq-initial-term-add-mul-nat-Ring :
    initial-term-add-mul-nat-Ring ＝ a
  eq-initial-term-add-mul-nat-Ring =
    ( ( ap
        ( add-Ring R a)
        ( inv (left-zero-law-mul-nat-scalar-Ring R d))) ∙
    ( right-unit-law-add-Ring R a))
```

## Properties

### Any arithmetic sequence in a semiring is homotopic to a standard arithmetic sequence

```agda
module _
  {l : Level} (R : Ring l)
  (u : arithmetic-sequence-Ring R)
  where

  htpy-seq-standard-arithmetic-sequence-Ring :
    ( seq-arithmetic-sequence-Ring R
      ( standard-arithmetic-sequence-Ring R
        ( initial-term-arithmetic-sequence-Ring R u)
        ( common-difference-arithmetic-sequence-Ring R u))) ~
    ( seq-arithmetic-sequence-Ring R u)
  htpy-seq-standard-arithmetic-sequence-Ring =
    htpy-seq-standard-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)
```

### The nth term of an arithmetic sequence with initial term `a` and common difference `d` is `a + n * d`

```agda
module _
  {l : Level} (R : Ring l) (a d : type-Ring R)
  where

  htpy-add-mul-standard-arithmetic-sequence-Ring :
    add-mul-nat-Ring R a d ~ seq-standard-arithmetic-sequence-Ring R a d
  htpy-add-mul-standard-arithmetic-sequence-Ring =
    htpy-add-mul-standard-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( a)
      ( d)
```

```agda
module _
  {l : Level} (R : Ring l) (u : arithmetic-sequence-Ring R)
  where

  hpty-add-mul-arithmetic-sequence-Ring :
    add-mul-nat-Ring
      ( R)
      ( initial-term-arithmetic-sequence-Ring R u)
      ( common-difference-arithmetic-sequence-Ring R u) ~
    seq-arithmetic-sequence-Ring R u
  hpty-add-mul-arithmetic-sequence-Ring =
    htpy-add-mul-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u)
```

### Constant sequences are arithmetic with common difference zero

```agda
module _
  {l : Level} (R : Ring l) (a : type-Ring R)
  where

  zero-is-common-difference-const-sequence-Ring :
    is-common-difference-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( λ _ → a)
      ( zero-Ring R)
  zero-is-common-difference-const-sequence-Ring =
    zero-is-common-difference-const-sequence-Semiring
      ( semiring-Ring R)
      ( a)

  arithmetic-const-sequence-Ring : arithmetic-sequence-Ring R
  arithmetic-const-sequence-Ring =
    arithmetic-const-sequence-Semiring
      ( semiring-Ring R)
      ( a)
```

### Being an arithmetic sequence in a ring is a property

```agda
module _
  {l : Level} (R : Ring l) (u : arithmetic-sequence-Ring R)
  where

  eq-is-arithmetic-arithmetic-sequence-Ring :
    ( H :
      is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( seq-arithmetic-sequence-Ring R u)) →
    is-arithmetic-seq-arithmetic-sequence-Ring R u ＝ H
  eq-is-arithmetic-arithmetic-sequence-Ring (d , H) =
    eq-type-subtype
      ( is-common-difference-prop-sequence-Semigroup
        ( additive-semigroup-Ring R)
        ( seq-arithmetic-sequence-Ring R u))
      ( ( inv
          ( compute-common-difference-arithmetic-sequence-Ring
          ( R)
          ( u))) ∙
        ( compute-common-difference-arithmetic-sequence-Ring
          ( R)
          ( seq-arithmetic-sequence-Ring R u , d , H)))

  is-contr-is-arithmetic-arithmetic-sequence-Ring :
    is-contr
      ( is-arithmetic-sequence-Semigroup
        ( additive-semigroup-Ring R)
        ( seq-arithmetic-sequence-Ring R u))
  is-contr-is-arithmetic-arithmetic-sequence-Ring =
    ( is-arithmetic-seq-arithmetic-sequence-Ring R u ,
      eq-is-arithmetic-arithmetic-sequence-Ring)

  is-prop-is-arithmetic-arithmetic-sequence-Ring :
    is-prop
      ( is-arithmetic-sequence-Semigroup
        ( additive-semigroup-Ring R)
        ( seq-arithmetic-sequence-Ring R u))
  is-prop-is-arithmetic-arithmetic-sequence-Ring =
    is-prop-is-contr is-contr-is-arithmetic-arithmetic-sequence-Ring

module _
  {l : Level} (R : Ring l) (u : ℕ → type-Ring R)
  where

  is-prop-is-arithmetic-sequence-Ring :
    is-prop
      ( is-arithmetic-sequence-Semigroup
        ( additive-semigroup-Ring R)
        ( u))
  is-prop-is-arithmetic-sequence-Ring =
    is-prop-has-element
      ( λ H → is-prop-is-arithmetic-arithmetic-sequence-Ring R (u , H))

  is-arithmetic-prop-sequence-Ring : Prop l
  pr1 is-arithmetic-prop-sequence-Ring =
    is-arithmetic-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( u)
  pr2 is-arithmetic-prop-sequence-Ring =
    is-prop-is-arithmetic-sequence-Ring
```

### Homotopic arithmetic sequences in rings are equal

```agda
module _
  {l : Level} (R : Ring l)
  (u v : arithmetic-sequence-Ring R)
  (H : seq-arithmetic-sequence-Ring R u ~ seq-arithmetic-sequence-Ring R v)
  where

  eq-htpy-arithmetic-sequence-Ring : u ＝ v
  eq-htpy-arithmetic-sequence-Ring =
    eq-type-subtype
      ( is-arithmetic-prop-sequence-Ring R)
      ( eq-htpy H)
```

### The negative of the common difference of an arithmetic sequence is a common difference of its negative

```agda
module _
  {l : Level} (R : Ring l) (u : arithmetic-sequence-Ring R)
  where

  is-common-difference-neg-arithmetic-sequence-Ring :
    is-common-difference-sequence-Semigroup
      ( additive-semigroup-Ring R)
      ( neg-function-Ring R ℕ (seq-arithmetic-sequence-Ring R u))
      ( neg-Ring R (common-difference-arithmetic-sequence-Ring R u))
  is-common-difference-neg-arithmetic-sequence-Ring n =
    ( ap (neg-Ring R) (is-common-difference-arithmetic-sequence-Ring R u n)) ∙
    ( distributive-neg-add-Ring R _ _)
```

### The type of arithmetic sequences in a ring is a subgroup of the additive group of sequences in the ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-is-arithmetic-add-sequence-Ring :
    {u v : ℕ → type-Ring R} →
    is-arithmetic-sequence-Ring R u →
    is-arithmetic-sequence-Ring R v →
    is-arithmetic-sequence-Ring
      ( R)
      ( add-function-Ring R ℕ u v)
  preserves-is-arithmetic-add-sequence-Ring {u} {v} H K =
    is-arithmetic-add-arithmetic-sequence-Semiring
      ( semiring-Ring R)
      ( u , H)
      ( v , K)

  preserves-is-arithmetic-neg-sequence-Ring :
    {u : ℕ → type-Ring R} →
    is-arithmetic-sequence-Ring R u →
    is-arithmetic-sequence-Ring
      ( R)
      ( neg-function-Ring R ℕ u)
  preserves-is-arithmetic-neg-sequence-Ring {u} (d , H) =
    ( neg-Ring R d ,
      is-common-difference-neg-arithmetic-sequence-Ring R (u , (d , H)))

  subgroup-add-arithmetic-sequence-Ring :
    Subgroup-Ab l (function-Ab (ab-Ring R) ℕ)
  pr1 subgroup-add-arithmetic-sequence-Ring =
    is-arithmetic-prop-sequence-Ring R
  pr1 (pr2 subgroup-add-arithmetic-sequence-Ring) =
    is-arithmetic-seq-arithmetic-sequence-Ring
      ( R)
      ( arithmetic-const-sequence-Ring R (zero-Ring R))
  pr2 (pr2 subgroup-add-arithmetic-sequence-Ring) =
    ( preserves-is-arithmetic-add-sequence-Ring ,
      preserves-is-arithmetic-neg-sequence-Ring)

  ab-subgroup-add-arithmetic=sequence-Ring : Ab l
  ab-subgroup-add-arithmetic=sequence-Ring =
    ab-Subgroup-Ab
      ( function-Ab (ab-Ring R) ℕ)
      ( subgroup-add-arithmetic-sequence-Ring)
```

## External links

- [Arithmetic progressions](https://en.wikipedia.org/wiki/Arithmetic_progression)
  at Wikipedia
