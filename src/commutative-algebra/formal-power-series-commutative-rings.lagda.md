# Formal power series in commutative rings

```agda
module commutative-algebra.formal-power-series-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.convolution-sequences-commutative-rings
open import commutative-algebra.formal-power-series-commutative-semirings
open import commutative-algebra.function-commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

A
{{#concept "formal power series" WD="formal power series" WDID=Q1003025 disambiguation="in a commutative ring" Agda=formal-power-series-Commutative-Ring}}
is a formal sum of the form `Σₙ aₙxⁿ`, without any notion of convergence.

## Definition

```agda
formal-power-series-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → UU l
formal-power-series-Commutative-Ring R =
  formal-power-series-Commutative-Semiring
    ( commutative-semiring-Commutative-Ring R)

formal-power-series-coefficients-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  sequence (type-Commutative-Ring R) → formal-power-series-Commutative-Ring R
formal-power-series-coefficients-Commutative-Ring R =
  formal-power-series-coefficients-Commutative-Semiring
```

## Properties

### The terms in the infinite sum of evaluating a formal power series at an argument

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  term-ev-formal-power-series-Commutative-Ring :
    (f : formal-power-series-Commutative-Ring R) →
    (x : type-Commutative-Ring R) →
    sequence (type-Commutative-Ring R)
  term-ev-formal-power-series-Commutative-Ring =
    term-ev-formal-power-series-Commutative-Semiring
```

### The set of formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  set-formal-power-series-Commutative-Ring : Set l
  set-formal-power-series-Commutative-Ring =
    set-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

### The constant zero formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  zero-formal-power-series-Commutative-Ring =
    zero-formal-power-series-Commutative-Semiring _
```

### The constant one formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  one-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  one-formal-power-series-Commutative-Ring =
    one-formal-power-series-Commutative-Semiring _
```

### The identity formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  id-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  id-formal-power-series-Commutative-Ring =
    id-formal-power-series-Commutative-Semiring _
```

### Addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R
  add-formal-power-series-Commutative-Ring =
    add-formal-power-series-Commutative-Semiring
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-add-formal-power-series-Commutative-Ring :
    (x y z : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring R
      ( add-formal-power-series-Commutative-Ring R x y)
      ( z) ＝
    add-formal-power-series-Commutative-Ring R
      ( x)
      ( add-formal-power-series-Commutative-Ring R y z)
  associative-add-formal-power-series-Commutative-Ring =
    associative-add-formal-power-series-Commutative-Semiring
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-add-formal-power-series-Commutative-Ring :
    (x y : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring R x y ＝
    add-formal-power-series-Commutative-Ring R y x
  commutative-add-formal-power-series-Commutative-Ring =
    commutative-add-formal-power-series-Commutative-Semiring
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-add-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring R
      ( zero-formal-power-series-Commutative-Ring R)
      ( x) ＝
    x
  left-unit-law-add-formal-power-series-Commutative-Ring =
    left-unit-law-add-formal-power-series-Commutative-Semiring

  right-unit-law-add-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring R
      ( x)
      ( zero-formal-power-series-Commutative-Ring R) ＝
    x
  right-unit-law-add-formal-power-series-Commutative-Ring =
    right-unit-law-add-formal-power-series-Commutative-Semiring
```

### Negation

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  neg-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R
  neg-formal-power-series-Commutative-Ring x =
    formal-power-series-coefficients-Commutative-Semiring
      ( λ n →
        neg-Commutative-Ring R
          ( coefficient-formal-power-series-Commutative-Semiring x n))
```

#### Inverse laws for addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-inverse-law-add-formal-power-series-Commutative-Ring :
      (x : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring R
        ( neg-formal-power-series-Commutative-Ring R x)
        ( x) ＝
      zero-formal-power-series-Commutative-Ring R
    left-inverse-law-add-formal-power-series-Commutative-Ring x =
      ap
        ( formal-power-series-coefficients-Commutative-Ring R)
        ( eq-htpy (λ n → left-inverse-law-add-Commutative-Ring R _))

    right-inverse-law-add-formal-power-series-Commutative-Ring :
      (x : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring R
        ( x)
        ( neg-formal-power-series-Commutative-Ring R x) ＝
      zero-formal-power-series-Commutative-Ring R
    right-inverse-law-add-formal-power-series-Commutative-Ring x =
      ap
        ( formal-power-series-coefficients-Commutative-Ring R)
        ( eq-htpy (λ n → right-inverse-law-add-Commutative-Ring R _))
```

### Multiplication

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  mul-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R
  mul-formal-power-series-Commutative-Ring =
    mul-formal-power-series-Commutative-Semiring
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-mul-formal-power-series-Commutative-Ring :
    (x y z : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( mul-formal-power-series-Commutative-Ring R x y)
      ( z) ＝
    mul-formal-power-series-Commutative-Ring R
      ( x)
      ( mul-formal-power-series-Commutative-Ring R y z)
  associative-mul-formal-power-series-Commutative-Ring =
    associative-mul-formal-power-series-Commutative-Semiring
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-mul-formal-power-series-Commutative-Ring :
    (x y : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R x y ＝
    mul-formal-power-series-Commutative-Ring R y x
  commutative-mul-formal-power-series-Commutative-Ring =
    commutative-mul-formal-power-series-Commutative-Semiring
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-mul-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( one-formal-power-series-Commutative-Ring R)
      ( x) ＝
    x
  left-unit-law-mul-formal-power-series-Commutative-Ring =
    left-unit-law-mul-formal-power-series-Commutative-Semiring

  right-unit-law-mul-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( x)
      ( one-formal-power-series-Commutative-Ring R) ＝
    x
  right-unit-law-mul-formal-power-series-Commutative-Ring =
    right-unit-law-mul-formal-power-series-Commutative-Semiring
```

#### Zero laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-zero-law-mul-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( zero-formal-power-series-Commutative-Ring R)
      ( x) ＝
    zero-formal-power-series-Commutative-Ring R
  left-zero-law-mul-formal-power-series-Commutative-Ring =
    left-zero-law-mul-formal-power-series-Commutative-Semiring

  right-zero-law-mul-formal-power-series-Commutative-Ring :
    (x : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( x)
      ( zero-formal-power-series-Commutative-Ring R) ＝
    zero-formal-power-series-Commutative-Ring R
  right-zero-law-mul-formal-power-series-Commutative-Ring =
    right-zero-law-mul-formal-power-series-Commutative-Semiring
```

### Distributive laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-add-formal-power-series-Commutative-Ring :
    (x y z : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( x)
      ( add-formal-power-series-Commutative-Ring R y z) ＝
    add-formal-power-series-Commutative-Ring R
      ( mul-formal-power-series-Commutative-Ring R x y)
      ( mul-formal-power-series-Commutative-Ring R x z)
  left-distributive-mul-add-formal-power-series-Commutative-Ring =
    left-distributive-mul-add-formal-power-series-Commutative-Semiring

  right-distributive-mul-add-formal-power-series-Commutative-Ring :
    (x y z : formal-power-series-Commutative-Ring R) →
    mul-formal-power-series-Commutative-Ring R
      ( add-formal-power-series-Commutative-Ring R x y)
      ( z) ＝
    add-formal-power-series-Commutative-Ring R
      ( mul-formal-power-series-Commutative-Ring R x z)
      ( mul-formal-power-series-Commutative-Ring R y z)
  right-distributive-mul-add-formal-power-series-Commutative-Ring =
    right-distributive-mul-add-formal-power-series-Commutative-Semiring
```

### The commutative ring of formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  additive-semigroup-formal-power-series-Commutative-Ring : Semigroup l
  additive-semigroup-formal-power-series-Commutative-Ring =
    additive-semigroup-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  additive-group-formal-power-series-Commutative-Ring : Group l
  additive-group-formal-power-series-Commutative-Ring =
    ( additive-semigroup-formal-power-series-Commutative-Ring ,
      ( zero-formal-power-series-Commutative-Ring R ,
        left-unit-law-add-formal-power-series-Commutative-Ring R ,
        right-unit-law-add-formal-power-series-Commutative-Ring R) ,
      neg-formal-power-series-Commutative-Ring R ,
      left-inverse-law-add-formal-power-series-Commutative-Ring R ,
      right-inverse-law-add-formal-power-series-Commutative-Ring R)

  additive-ab-formal-power-series-Commutative-Ring : Ab l
  additive-ab-formal-power-series-Commutative-Ring =
    ( additive-group-formal-power-series-Commutative-Ring ,
      commutative-add-formal-power-series-Commutative-Ring R)

  ring-formal-power-series-Commutative-Ring : Ring l
  ring-formal-power-series-Commutative-Ring =
    ( additive-ab-formal-power-series-Commutative-Ring ,
      ( mul-formal-power-series-Commutative-Ring R ,
        associative-mul-formal-power-series-Commutative-Ring R) ,
      ( one-formal-power-series-Commutative-Ring R ,
        left-unit-law-mul-formal-power-series-Commutative-Ring R ,
        right-unit-law-mul-formal-power-series-Commutative-Ring R) ,
      left-distributive-mul-add-formal-power-series-Commutative-Ring R ,
      right-distributive-mul-add-formal-power-series-Commutative-Ring R)

  commutative-ring-formal-power-series-Commutative-Ring : Commutative-Ring l
  commutative-ring-formal-power-series-Commutative-Ring =
    ( ring-formal-power-series-Commutative-Ring ,
      commutative-mul-formal-power-series-Commutative-Ring R)
```
