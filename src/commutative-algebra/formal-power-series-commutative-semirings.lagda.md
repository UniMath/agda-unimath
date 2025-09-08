# Formal power series in commutative semirings

```agda
module commutative-algebra.formal-power-series-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.convolution-sequences-commutative-semirings
open import commutative-algebra.function-commutative-semirings
open import commutative-algebra.powers-of-elements-commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.semirings
```

</details>

## Idea

A
{{#concept "formal power series" WD="formal power series" WDID=Q1003025 disambiguation="in a commutative semiring" Agda=formal-power-series-Commutative-Semiring}}
is a formal sum of the form `Σₙ aₙxⁿ`, without any notion of convergence.

## Definition

Formal power series are defined with a record to make them intensionally
distinct from the sequence of their coefficients.

```agda
record
  formal-power-series-Commutative-Semiring
    {l : Level} (R : Commutative-Semiring l) : UU l
  where

  constructor formal-power-series-coefficients-Commutative-Semiring

  field
    coefficient-formal-power-series-Commutative-Semiring :
      sequence (type-Commutative-Semiring R)

open formal-power-series-Commutative-Semiring public
```

## Properties

### The terms in the infinite sum of evaluating a formal power series at an argument

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  term-ev-formal-power-series-Commutative-Semiring :
    (f : formal-power-series-Commutative-Semiring R) →
    (x : type-Commutative-Semiring R) →
    sequence (type-Commutative-Semiring R)
  term-ev-formal-power-series-Commutative-Semiring
    ( formal-power-series-coefficients-Commutative-Semiring a)
    ( x)
    ( n) =
    mul-Commutative-Semiring R (a n) (power-Commutative-Semiring R n x)
```

### Equivalence to sequences in the commutative semiring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  equiv-formal-power-series-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R) ≃
    formal-power-series-Commutative-Semiring R
  equiv-formal-power-series-sequence-Commutative-Semiring =
    ( formal-power-series-coefficients-Commutative-Semiring ,
      is-equiv-is-invertible
        ( coefficient-formal-power-series-Commutative-Semiring)
        ( λ _ → refl)
        ( λ _ → refl))
```

### The set of formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  abstract
    is-set-formal-power-series-Commutative-Semiring :
      is-set (formal-power-series-Commutative-Semiring R)
    is-set-formal-power-series-Commutative-Semiring =
      is-set-equiv
        ( _)
        ( inv-equiv (equiv-formal-power-series-sequence-Commutative-Semiring R))
        ( is-set-type-Π-Set' _ (λ _ → set-Commutative-Semiring R))

  set-formal-power-series-Commutative-Semiring : Set l
  set-formal-power-series-Commutative-Semiring =
    ( formal-power-series-Commutative-Semiring R ,
      is-set-formal-power-series-Commutative-Semiring)
```

### The constant zero formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  zero-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R
  zero-formal-power-series-Commutative-Semiring =
    formal-power-series-coefficients-Commutative-Semiring
      ( zero-Commutative-Semiring
        ( commutative-semiring-convolution-sequence-Commutative-Semiring R))
```

### The constant one formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  one-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R
  one-formal-power-series-Commutative-Semiring =
    formal-power-series-coefficients-Commutative-Semiring
      ( one-Commutative-Semiring
        ( commutative-semiring-convolution-sequence-Commutative-Semiring R))
```

### The identity formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  id-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R
  id-formal-power-series-Commutative-Semiring =
    formal-power-series-coefficients-Commutative-Semiring
      ( λ where
          zero-ℕ → zero-Commutative-Semiring R
          (succ-ℕ zero-ℕ) → one-Commutative-Semiring R
          (succ-ℕ (succ-ℕ _)) → zero-Commutative-Semiring R)
```

### Addition

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  add-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R →
    formal-power-series-Commutative-Semiring R →
    formal-power-series-Commutative-Semiring R
  add-formal-power-series-Commutative-Semiring x y =
    formal-power-series-coefficients-Commutative-Semiring
      ( add-Commutative-Semiring
        ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y))
```

#### Associativity

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    associative-add-formal-power-series-Commutative-Semiring :
      (x y z : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( add-formal-power-series-Commutative-Semiring x y)
        ( z) ＝
      add-formal-power-series-Commutative-Semiring
        ( x)
        ( add-formal-power-series-Commutative-Semiring y z)
    associative-add-formal-power-series-Commutative-Semiring x y z =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( associative-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y)
          ( coefficient-formal-power-series-Commutative-Semiring z))
```

#### Commutativity

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    commutative-add-formal-power-series-Commutative-Semiring :
      (x y : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring x y ＝
      add-formal-power-series-Commutative-Semiring y x
    commutative-add-formal-power-series-Commutative-Semiring x y =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( commutative-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y))
```

#### Unit laws

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    left-unit-law-add-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( zero-formal-power-series-Commutative-Semiring R)
        ( x) ＝
      x
    left-unit-law-add-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( left-unit-law-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))

    right-unit-law-add-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      add-formal-power-series-Commutative-Semiring
        ( x)
        ( zero-formal-power-series-Commutative-Semiring R) ＝
      x
    right-unit-law-add-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( right-unit-law-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))
```

### Multiplication

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  mul-formal-power-series-Commutative-Semiring :
    formal-power-series-Commutative-Semiring R →
    formal-power-series-Commutative-Semiring R →
    formal-power-series-Commutative-Semiring R
  mul-formal-power-series-Commutative-Semiring x y =
    formal-power-series-coefficients-Commutative-Semiring
      ( mul-Commutative-Semiring
        ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y))
```

#### Associativity

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    associative-mul-formal-power-series-Commutative-Semiring :
      (x y z : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( mul-formal-power-series-Commutative-Semiring x y)
        ( z) ＝
      mul-formal-power-series-Commutative-Semiring
        ( x)
        ( mul-formal-power-series-Commutative-Semiring y z)
    associative-mul-formal-power-series-Commutative-Semiring x y z =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( associative-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y)
          ( coefficient-formal-power-series-Commutative-Semiring z))
```

#### Commutativity

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    commutative-mul-formal-power-series-Commutative-Semiring :
      (x y : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring x y ＝
      mul-formal-power-series-Commutative-Semiring y x
    commutative-mul-formal-power-series-Commutative-Semiring x y =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( commutative-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y))
```

#### Unit laws

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    left-unit-law-mul-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( one-formal-power-series-Commutative-Semiring R)
        ( x) ＝
      x
    left-unit-law-mul-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( left-unit-law-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))

    right-unit-law-mul-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( x)
        ( one-formal-power-series-Commutative-Semiring R) ＝
      x
    right-unit-law-mul-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( right-unit-law-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))
```

#### Zero laws

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    left-zero-law-mul-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( zero-formal-power-series-Commutative-Semiring R)
        ( x) ＝
      zero-formal-power-series-Commutative-Semiring R
    left-zero-law-mul-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( left-zero-law-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))

    right-zero-law-mul-formal-power-series-Commutative-Semiring :
      (x : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( x)
        ( zero-formal-power-series-Commutative-Semiring R) ＝
      zero-formal-power-series-Commutative-Semiring R
    right-zero-law-mul-formal-power-series-Commutative-Semiring x =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( right-zero-law-mul-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x))
```

### Distributive laws

```agda
module _
  {l : Level} {R : Commutative-Semiring l}
  where

  abstract
    left-distributive-mul-add-formal-power-series-Commutative-Semiring :
      (x y z : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( x)
        ( add-formal-power-series-Commutative-Semiring y z) ＝
      add-formal-power-series-Commutative-Semiring
        ( mul-formal-power-series-Commutative-Semiring x y)
        ( mul-formal-power-series-Commutative-Semiring x z)
    left-distributive-mul-add-formal-power-series-Commutative-Semiring x y z =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( left-distributive-mul-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y)
          ( coefficient-formal-power-series-Commutative-Semiring z))

    right-distributive-mul-add-formal-power-series-Commutative-Semiring :
      (x y z : formal-power-series-Commutative-Semiring R) →
      mul-formal-power-series-Commutative-Semiring
        ( add-formal-power-series-Commutative-Semiring x y)
        ( z) ＝
      add-formal-power-series-Commutative-Semiring
        ( mul-formal-power-series-Commutative-Semiring x z)
        ( mul-formal-power-series-Commutative-Semiring y z)
    right-distributive-mul-add-formal-power-series-Commutative-Semiring x y z =
      ap
        ( formal-power-series-coefficients-Commutative-Semiring)
        ( right-distributive-mul-add-Commutative-Semiring
          ( commutative-semiring-convolution-sequence-Commutative-Semiring R)
          ( coefficient-formal-power-series-Commutative-Semiring x)
          ( coefficient-formal-power-series-Commutative-Semiring y)
          ( coefficient-formal-power-series-Commutative-Semiring z))
```

### The commutative semiring of formal power series

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  additive-semigroup-formal-power-series-Commutative-Semiring : Semigroup l
  additive-semigroup-formal-power-series-Commutative-Semiring =
    ( set-formal-power-series-Commutative-Semiring R ,
      add-formal-power-series-Commutative-Semiring ,
      associative-add-formal-power-series-Commutative-Semiring)

  additive-monoid-formal-power-series-Commutative-Semiring : Monoid l
  additive-monoid-formal-power-series-Commutative-Semiring =
    ( additive-semigroup-formal-power-series-Commutative-Semiring ,
      zero-formal-power-series-Commutative-Semiring R ,
      left-unit-law-add-formal-power-series-Commutative-Semiring ,
      right-unit-law-add-formal-power-series-Commutative-Semiring)

  additive-commutative-monoid-formal-power-series-Commutative-Semiring :
    Commutative-Monoid l
  additive-commutative-monoid-formal-power-series-Commutative-Semiring =
    ( additive-monoid-formal-power-series-Commutative-Semiring ,
      commutative-add-formal-power-series-Commutative-Semiring)

  semiring-formal-power-series-Commutative-Semiring : Semiring l
  semiring-formal-power-series-Commutative-Semiring =
    ( additive-commutative-monoid-formal-power-series-Commutative-Semiring ,
      ( ( mul-formal-power-series-Commutative-Semiring ,
          associative-mul-formal-power-series-Commutative-Semiring) ,
        ( one-formal-power-series-Commutative-Semiring R ,
          left-unit-law-mul-formal-power-series-Commutative-Semiring ,
          right-unit-law-mul-formal-power-series-Commutative-Semiring) ,
        left-distributive-mul-add-formal-power-series-Commutative-Semiring ,
        right-distributive-mul-add-formal-power-series-Commutative-Semiring) ,
      left-zero-law-mul-formal-power-series-Commutative-Semiring ,
      right-zero-law-mul-formal-power-series-Commutative-Semiring)

  commutative-semiring-formal-power-series-Commutative-Semiring :
    Commutative-Semiring l
  commutative-semiring-formal-power-series-Commutative-Semiring =
    ( semiring-formal-power-series-Commutative-Semiring ,
      commutative-mul-formal-power-series-Commutative-Semiring)
```
