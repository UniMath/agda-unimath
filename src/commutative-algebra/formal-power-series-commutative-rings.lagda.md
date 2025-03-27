# Formal power series on commutative rings

```agda
module commutative-algebra.formal-power-series-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.formal-power-series-commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

A
{{#concept "formal power series" Agda=formal-power-series-Commutative-Ring WDID=Q1003025 WD="formal power series"}}
in a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
symbolic infinite sum over all `n : ℕ` of `cₙ xⁿ`, where `cₙ : R`. Convergence
of this sum is not relevant, but with the standard definitions of addition and
multiplication for power series, this forms a new commutative ring.

## Definition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  formal-power-series-Commutative-Ring : UU l
  formal-power-series-Commutative-Ring =
    formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  formal-power-series-coefficients-Commutative-Ring :
    (ℕ → type-Commutative-Ring R) →
    formal-power-series-Commutative-Ring
  formal-power-series-coefficients-Commutative-Ring =
    formal-power-series-coefficients-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  coefficient-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring → ℕ → type-Commutative-Ring R
  coefficient-formal-power-series-Commutative-Ring =
    coefficient-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  coefficient-formal-power-series-coefficients-Commutative-Ring :
    (c : ℕ → type-Commutative-Ring R) →
    coefficient-formal-power-series-Commutative-Ring
      (formal-power-series-coefficients-Commutative-Ring c) ~ c
  coefficient-formal-power-series-coefficients-Commutative-Ring =
    coefficient-formal-power-series-coefficients-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  eq-formal-power-series-coefficients-Commutative-Ring :
    (p : formal-power-series-Commutative-Ring) →
    p ＝
    formal-power-series-coefficients-Commutative-Ring
      ( coefficient-formal-power-series-Commutative-Ring p)
  eq-formal-power-series-coefficients-Commutative-Ring =
    eq-formal-power-series-coefficients-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  eq-htpy-coefficients-formal-power-series-Commutative-Ring :
    ( p q : formal-power-series-Commutative-Ring) →
    ( coefficient-formal-power-series-Commutative-Ring p ~
      coefficient-formal-power-series-Commutative-Ring q) →
    p ＝ q
  eq-htpy-coefficients-formal-power-series-Commutative-Ring =
    eq-htpy-coefficients-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  is-set-formal-power-series-Commutative-Ring :
    is-set formal-power-series-Commutative-Ring
  is-set-formal-power-series-Commutative-Ring =
    is-set-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  set-formal-power-series-Commutative-Ring : Set l
  set-formal-power-series-Commutative-Ring =
    set-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

## Operations

### Zero formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  zero-formal-power-series-Commutative-Ring =
    zero-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  eq-coefficient-zero-formal-power-series-Commutative-Ring :
    zero-formal-power-series-Commutative-Ring ＝
    formal-power-series-coefficients-Commutative-Ring
      ( R)
      ( λ _ → zero-Commutative-Ring R)
  eq-coefficient-zero-formal-power-series-Commutative-Ring =
    eq-coefficient-zero-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  htpy-coefficient-zero-formal-power-series-Commutative-Ring :
    coefficient-formal-power-series-Commutative-Ring
      ( R)
      ( zero-formal-power-series-Commutative-Ring) ~
    ( λ _ → zero-Commutative-Ring R)
  htpy-coefficient-zero-formal-power-series-Commutative-Ring =
    htpy-coefficient-zero-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

### Constant formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  coefficient-constant-formal-power-series-Commutative-Ring :
    type-Commutative-Ring R → ℕ → type-Commutative-Ring R
  coefficient-constant-formal-power-series-Commutative-Ring =
    coefficient-constant-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  coefficient-nonzero-constant-formal-power-series-Commutative-Ring :
    (c : type-Commutative-Ring R) → (n : ℕ) → is-nonzero-ℕ n →
    is-zero-Commutative-Ring R
      ( coefficient-constant-formal-power-series-Commutative-Ring c n)
  coefficient-nonzero-constant-formal-power-series-Commutative-Ring =
    coefficient-nonzero-constant-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  constant-formal-power-series-Commutative-Ring :
    type-Commutative-Ring R → formal-power-series-Commutative-Ring R
  constant-formal-power-series-Commutative-Ring =
    constant-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  eq-coefficient-constant-formal-power-series-Commutative-Ring :
    (c : type-Commutative-Ring R) →
    constant-formal-power-series-Commutative-Ring c ＝
    formal-power-series-coefficients-Commutative-Ring
      ( R)
      ( coefficient-constant-formal-power-series-Commutative-Ring c)
  eq-coefficient-constant-formal-power-series-Commutative-Ring =
    eq-coefficient-constant-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  one-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  one-formal-power-series-Commutative-Ring =
    one-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

#### The zero formal power series is the constant formal power series for zero

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  eq-zero-constant-formal-power-series-Commutative-Ring :
    constant-formal-power-series-Commutative-Ring R (zero-Commutative-Ring R) ＝
    zero-formal-power-series-Commutative-Ring R
  eq-zero-constant-formal-power-series-Commutative-Ring =
    eq-zero-constant-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

### Addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  coefficient-add-formal-power-series-Commutative-Ring :
    (p q : formal-power-series-Commutative-Ring R) (n : ℕ) →
    type-Commutative-Ring R
  coefficient-add-formal-power-series-Commutative-Ring =
    coefficient-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  add-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R →
    formal-power-series-Commutative-Ring R
  add-formal-power-series-Commutative-Ring =
    add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  eq-coefficient-add-formal-power-series-Commutative-Ring :
    (p q : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring p q ＝
    formal-power-series-coefficients-Commutative-Ring
      ( R)
      ( coefficient-add-formal-power-series-Commutative-Ring p q)
  eq-coefficient-add-formal-power-series-Commutative-Ring =
    eq-coefficient-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  htpy-coefficient-add-formal-power-series-Commutative-Ring :
    (p q : formal-power-series-Commutative-Ring R) →
    coefficient-formal-power-series-Commutative-Ring
      ( R)
      ( add-formal-power-series-Commutative-Ring p q) ~
    coefficient-add-formal-power-series-Commutative-Ring p q
  htpy-coefficient-add-formal-power-series-Commutative-Ring =
    htpy-coefficient-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  commutative-add-formal-power-series-Commutative-Ring :
    (p q : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring R p q ＝
    add-formal-power-series-Commutative-Ring R q p
  commutative-add-formal-power-series-Commutative-Ring =
    commutative-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-unit-law-add-formal-power-series-Commutative-Ring :
    (p : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring
      ( R)
      ( zero-formal-power-series-Commutative-Ring R)
      ( p) ＝ p
  left-unit-law-add-formal-power-series-Commutative-Ring =
    left-unit-law-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  right-unit-law-add-formal-power-series-Commutative-Ring :
    (p : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring
      ( R)
      ( p)
      ( zero-formal-power-series-Commutative-Ring R) ＝ p
  right-unit-law-add-formal-power-series-Commutative-Ring =
    right-unit-law-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  associative-add-formal-power-series-Commutative-Ring :
    (p q r : formal-power-series-Commutative-Ring R) →
    add-formal-power-series-Commutative-Ring
      ( R)
      ( add-formal-power-series-Commutative-Ring R p q)
      ( r) ＝
    add-formal-power-series-Commutative-Ring
      ( R)
      ( p)
      ( add-formal-power-series-Commutative-Ring R q r)
  associative-add-formal-power-series-Commutative-Ring =
    associative-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

### Negation

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p : formal-power-series-Commutative-Ring R)
  where

  opaque
    neg-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring R
    neg-formal-power-series-Commutative-Ring =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( neg-Commutative-Ring R ∘
          coefficient-formal-power-series-Commutative-Ring R p)

    htpy-coefficient-neg-formal-power-series-Commutative-Ring :
      coefficient-formal-power-series-Commutative-Ring
        ( R)
        ( neg-formal-power-series-Commutative-Ring) ~
      neg-Commutative-Ring R ∘
      coefficient-formal-power-series-Commutative-Ring R p
    htpy-coefficient-neg-formal-power-series-Commutative-Ring =
      coefficient-formal-power-series-coefficients-Commutative-Ring R _

    eq-coefficient-neg-formal-power-series-Commutative-Ring :
      neg-formal-power-series-Commutative-Ring ＝
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( neg-Commutative-Ring R ∘
          coefficient-formal-power-series-Commutative-Ring R p)
    eq-coefficient-neg-formal-power-series-Commutative-Ring = refl
```

#### Inverse laws for addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p : formal-power-series-Commutative-Ring R)
  where

  abstract
    left-inverse-law-add-formal-power-series-Commutative-Ring :
      add-formal-power-series-Commutative-Ring
        ( R)
        ( neg-formal-power-series-Commutative-Ring R p)
        ( p) ＝
      zero-formal-power-series-Commutative-Ring R
    left-inverse-law-add-formal-power-series-Commutative-Ring =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( λ n →
          htpy-coefficient-add-formal-power-series-Commutative-Ring R _ _ n ∙
          ap-add-Commutative-Ring
            ( R)
            ( htpy-coefficient-neg-formal-power-series-Commutative-Ring R p n)
            ( refl) ∙
          left-inverse-law-add-Commutative-Ring R _ ∙
          inv (htpy-coefficient-zero-formal-power-series-Commutative-Ring R n))

    right-inverse-law-add-formal-power-series-Commutative-Ring :
      add-formal-power-series-Commutative-Ring
        ( R)
        ( p)
        ( neg-formal-power-series-Commutative-Ring R p) ＝
      zero-formal-power-series-Commutative-Ring R
    right-inverse-law-add-formal-power-series-Commutative-Ring =
      commutative-add-formal-power-series-Commutative-Ring R _ _ ∙
      left-inverse-law-add-formal-power-series-Commutative-Ring
```

#### The additive Abelian group of formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  semigroup-add-formal-power-series-Commutative-Ring : Semigroup l
  semigroup-add-formal-power-series-Commutative-Ring =
    semigroup-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  is-unital-add-formal-power-series-Commutative-Ring :
    is-unital (add-formal-power-series-Commutative-Ring R)
  is-unital-add-formal-power-series-Commutative-Ring =
    is-unital-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  monoid-add-formal-power-series-Commutative-Ring : Monoid l
  monoid-add-formal-power-series-Commutative-Ring =
    monoid-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  commutative-monoid-add-formal-power-series-Commutative-Ring :
    Commutative-Monoid l
  commutative-monoid-add-formal-power-series-Commutative-Ring =
    commutative-monoid-add-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  group-add-formal-power-series-Commutative-Ring : Group l
  group-add-formal-power-series-Commutative-Ring =
    semigroup-add-formal-power-series-Commutative-Ring ,
    is-unital-add-formal-power-series-Commutative-Ring ,
    neg-formal-power-series-Commutative-Ring R ,
    left-inverse-law-add-formal-power-series-Commutative-Ring R ,
    right-inverse-law-add-formal-power-series-Commutative-Ring R

  abelian-group-add-formal-power-series-Commutative-Ring : Ab l
  abelian-group-add-formal-power-series-Commutative-Ring =
    group-add-formal-power-series-Commutative-Ring ,
    commutative-add-formal-power-series-Commutative-Ring R
```

### Multiplication

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p q : formal-power-series-Commutative-Ring R)
  where

  coefficient-mul-formal-power-series-Commutative-Ring :
    ℕ → type-Commutative-Ring R
  coefficient-mul-formal-power-series-Commutative-Ring =
    coefficient-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
      ( q)

  mul-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  mul-formal-power-series-Commutative-Ring =
    mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
      ( q)

  eq-coefficient-mul-formal-power-series-Commutative-Ring :
    coefficient-formal-power-series-Commutative-Ring
      ( R)
      ( mul-formal-power-series-Commutative-Ring) ~
    coefficient-mul-formal-power-series-Commutative-Ring
  eq-coefficient-mul-formal-power-series-Commutative-Ring =
    eq-coefficient-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
      ( q)
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p q : formal-power-series-Commutative-Ring R)
  where

  commutative-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring R p q ＝
    mul-formal-power-series-Commutative-Ring R q p
  commutative-mul-formal-power-series-Commutative-Ring =
    commutative-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
      ( q)
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p q r : formal-power-series-Commutative-Ring R)
  where

  associative-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( mul-formal-power-series-Commutative-Ring R p q)
      ( r) ＝
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( p)
      ( mul-formal-power-series-Commutative-Ring R q r)
  associative-mul-formal-power-series-Commutative-Ring =
    associative-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
      ( q)
      ( r)
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p : formal-power-series-Commutative-Ring R)
  where

  left-unit-law-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( one-formal-power-series-Commutative-Ring R)
      ( p) ＝ p
  left-unit-law-mul-formal-power-series-Commutative-Ring =
    left-unit-law-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)

  right-unit-law-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( p)
      ( one-formal-power-series-Commutative-Ring R) ＝ p
  right-unit-law-mul-formal-power-series-Commutative-Ring =
    right-unit-law-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
```

#### Zero laws of multiplication

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p : formal-power-series-Commutative-Ring R)
  where

  left-zero-law-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( zero-formal-power-series-Commutative-Ring R)
      ( p) ＝
    zero-formal-power-series-Commutative-Ring R
  left-zero-law-mul-formal-power-series-Commutative-Ring =
    left-zero-law-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)

  right-zero-law-mul-formal-power-series-Commutative-Ring :
    mul-formal-power-series-Commutative-Ring
      ( R)
      ( p)
      ( zero-formal-power-series-Commutative-Ring R) ＝
    zero-formal-power-series-Commutative-Ring R
  right-zero-law-mul-formal-power-series-Commutative-Ring =
    right-zero-law-mul-formal-power-series-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( p)
```

#### Distributivity of multiplication over addition

```agda
left-distributive-mul-add-formal-power-series-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  (p q r : formal-power-series-Commutative-Ring R) →
  mul-formal-power-series-Commutative-Ring
    ( R)
    ( p)
    ( add-formal-power-series-Commutative-Ring R q r) ＝
  add-formal-power-series-Commutative-Ring
    ( R)
    ( mul-formal-power-series-Commutative-Ring R p q)
    ( mul-formal-power-series-Commutative-Ring R p r)
left-distributive-mul-add-formal-power-series-Commutative-Ring R =
  left-distributive-mul-add-formal-power-series-Commutative-Semiring
    ( commutative-semiring-Commutative-Ring R)

right-distributive-mul-add-formal-power-series-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  (p q r : formal-power-series-Commutative-Ring R) →
  mul-formal-power-series-Commutative-Ring
    ( R)
    ( add-formal-power-series-Commutative-Ring R p q)
    ( r) ＝
  add-formal-power-series-Commutative-Ring
    ( R)
    ( mul-formal-power-series-Commutative-Ring R p r)
    ( mul-formal-power-series-Commutative-Ring R q r)
right-distributive-mul-add-formal-power-series-Commutative-Ring R =
  right-distributive-mul-add-formal-power-series-Commutative-Semiring
    ( commutative-semiring-Commutative-Ring R)
```

### The commutative ring of formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  has-associative-mul-formal-power-series-Commutative-Ring :
    has-associative-mul (formal-power-series-Commutative-Ring R)
  has-associative-mul-formal-power-series-Commutative-Ring =
    mul-formal-power-series-Commutative-Ring R ,
    associative-mul-formal-power-series-Commutative-Ring R

  unit-laws-mul-formal-power-series-Commutative-Ring :
    unit-laws
      ( mul-formal-power-series-Commutative-Ring R)
      ( one-formal-power-series-Commutative-Ring R)
  unit-laws-mul-formal-power-series-Commutative-Ring =
    left-unit-law-mul-formal-power-series-Commutative-Ring R ,
    right-unit-law-mul-formal-power-series-Commutative-Ring R

  is-unital-mul-formal-power-series-Commutative-Ring :
    is-unital (mul-formal-power-series-Commutative-Ring R)
  is-unital-mul-formal-power-series-Commutative-Ring =
    one-formal-power-series-Commutative-Ring R ,
    unit-laws-mul-formal-power-series-Commutative-Ring

  semiring-formal-power-series-Commutative-Ring : Semiring l
  semiring-formal-power-series-Commutative-Ring =
    commutative-monoid-add-formal-power-series-Commutative-Ring R ,
    ( has-associative-mul-formal-power-series-Commutative-Ring ,
      is-unital-mul-formal-power-series-Commutative-Ring ,
      left-distributive-mul-add-formal-power-series-Commutative-Ring R ,
      right-distributive-mul-add-formal-power-series-Commutative-Ring R) ,
    left-zero-law-mul-formal-power-series-Commutative-Ring R ,
    right-zero-law-mul-formal-power-series-Commutative-Ring R

  commutative-semiring-formal-power-series-Commutative-Ring :
    Commutative-Semiring l
  commutative-semiring-formal-power-series-Commutative-Ring =
    semiring-formal-power-series-Commutative-Ring ,
    commutative-mul-formal-power-series-Commutative-Ring R

  ring-formal-power-series-Commutative-Ring : Ring l
  ring-formal-power-series-Commutative-Ring =
    abelian-group-add-formal-power-series-Commutative-Ring R ,
    has-associative-mul-formal-power-series-Commutative-Ring ,
    is-unital-mul-formal-power-series-Commutative-Ring ,
    left-distributive-mul-add-formal-power-series-Commutative-Ring R ,
    right-distributive-mul-add-formal-power-series-Commutative-Ring R

  commutative-ring-formal-power-series-Commutative-Ring : Commutative-Ring l
  commutative-ring-formal-power-series-Commutative-Ring =
    ring-formal-power-series-Commutative-Ring ,
    commutative-mul-formal-power-series-Commutative-Ring R
```
