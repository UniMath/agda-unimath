# Formal power series rings

```agda
module commutative-algebra.formal-power-series-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.involutions
open import foundation.sets
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
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

  opaque
    formal-power-series-Commutative-Ring : UU l
    formal-power-series-Commutative-Ring = ℕ → type-Commutative-Ring R

    formal-power-series-coefficients-Commutative-Ring :
      (ℕ → type-Commutative-Ring R) → formal-power-series-Commutative-Ring
    formal-power-series-coefficients-Commutative-Ring = id

    coefficient-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring → ℕ → type-Commutative-Ring R
    coefficient-formal-power-series-Commutative-Ring = id

    coefficient-formal-power-series-coefficients-Commutative-Ring :
      (c : ℕ → type-Commutative-Ring R) →
      coefficient-formal-power-series-Commutative-Ring
        (formal-power-series-coefficients-Commutative-Ring c) ~ c
    coefficient-formal-power-series-coefficients-Commutative-Ring _ _ = refl

    eq-htpy-coefficients-formal-power-series-Commutative-Ring :
      ( p q : formal-power-series-Commutative-Ring) →
      ( coefficient-formal-power-series-Commutative-Ring p ~
        coefficient-formal-power-series-Commutative-Ring q) →
      p ＝ q
    eq-htpy-coefficients-formal-power-series-Commutative-Ring _ _ = eq-htpy

    is-set-formal-power-series-Commutative-Ring :
      is-set formal-power-series-Commutative-Ring
    is-set-formal-power-series-Commutative-Ring =
      is-set-function-type (is-set-type-Set (set-Commutative-Ring R))

  set-formal-power-series-Commutative-Ring : Set l
  set-formal-power-series-Commutative-Ring =
    formal-power-series-Commutative-Ring ,
    is-set-formal-power-series-Commutative-Ring
```

## Operations

### Zero formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    zero-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring R
    zero-formal-power-series-Commutative-Ring =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( λ _ → zero-Commutative-Ring R)

    is-zero-coefficient-zero-formal-power-series-Commutative-Ring :
      (n : ℕ) →
      is-zero-Commutative-Ring
        ( R)
        ( coefficient-formal-power-series-Commutative-Ring
          ( R)
          ( zero-formal-power-series-Commutative-Ring)
          ( n))
    is-zero-coefficient-zero-formal-power-series-Commutative-Ring =
      coefficient-formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( λ _ → zero-Commutative-Ring R)
```

### Constant formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  coefficient-constant-formal-power-series-Commutative-Ring :
    type-Commutative-Ring R → ℕ → type-Commutative-Ring R
  coefficient-constant-formal-power-series-Commutative-Ring c zero-ℕ = c
  coefficient-constant-formal-power-series-Commutative-Ring c (succ-ℕ _) =
    zero-Commutative-Ring R

  abstract
    constant-formal-power-series-Commutative-Ring :
      type-Commutative-Ring R → formal-power-series-Commutative-Ring R
    constant-formal-power-series-Commutative-Ring c =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( coefficient-constant-formal-power-series-Commutative-Ring c)

    eq-coefficient-constant-formal-power-series-Commutative-Ring :
      (c : type-Commutative-Ring R) →
      coefficient-formal-power-series-Commutative-Ring
        ( R)
        ( constant-formal-power-series-Commutative-Ring c) ~
      coefficient-constant-formal-power-series-Commutative-Ring c
    eq-coefficient-constant-formal-power-series-Commutative-Ring c =
      coefficient-formal-power-series-coefficients-Commutative-Ring R _

  one-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R
  one-formal-power-series-Commutative-Ring =
    constant-formal-power-series-Commutative-Ring (one-Commutative-Ring R)
```

#### The zero formal power series is the constant formal power series for zero

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  eq-zero-coefficient-constant-formal-power-series-Commutative-Ring :
    (n : ℕ) →
    is-zero-Commutative-Ring
      ( R)
      ( coefficient-constant-formal-power-series-Commutative-Ring
        ( R)
        ( zero-Commutative-Ring R)
        ( n))
  eq-zero-coefficient-constant-formal-power-series-Commutative-Ring zero-ℕ =
    refl
  eq-zero-coefficient-constant-formal-power-series-Commutative-Ring (succ-ℕ _) =
    refl

  eq-zero-constant-formal-power-series-Commutative-Ring :
    constant-formal-power-series-Commutative-Ring R (zero-Commutative-Ring R) ＝
    zero-formal-power-series-Commutative-Ring R
  eq-zero-constant-formal-power-series-Commutative-Ring =
    eq-htpy-coefficients-formal-power-series-Commutative-Ring
      ( R)
      ( _)
      ( _)
      ( eq-coefficient-constant-formal-power-series-Commutative-Ring R _ ∙h
        eq-zero-coefficient-constant-formal-power-series-Commutative-Ring ∙h
        inv-htpy
          ( is-zero-coefficient-zero-formal-power-series-Commutative-Ring R))
```

### Negation

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  coefficient-neg-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R → ℕ → type-Commutative-Ring R
  coefficient-neg-formal-power-series-Commutative-Ring p n =
    neg-Commutative-Ring
      ( R)
      ( coefficient-formal-power-series-Commutative-Ring R p n)

  abstract
    neg-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring R →
      formal-power-series-Commutative-Ring R
    neg-formal-power-series-Commutative-Ring p =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( coefficient-neg-formal-power-series-Commutative-Ring p)

    eq-coefficient-neg-formal-power-series-Commutative-Ring :
      (p : formal-power-series-Commutative-Ring R) →
      coefficient-formal-power-series-Commutative-Ring
        ( R)
        ( neg-formal-power-series-Commutative-Ring p) ~
      coefficient-neg-formal-power-series-Commutative-Ring p
    eq-coefficient-neg-formal-power-series-Commutative-Ring p =
      coefficient-formal-power-series-coefficients-Commutative-Ring R _
```

#### The negation of a constant formal power series is the constant formal power series of the negation

```agda
module _
  {l : Level} (R : Commutative-Ring l) (c : type-Commutative-Ring R)
  where

  abstract
    htpy-coefficients-neg-constant-formal-power-series-Commutative-Ring :
      (n : ℕ) →
      coefficient-neg-formal-power-series-Commutative-Ring
        ( R)
        ( constant-formal-power-series-Commutative-Ring R c)
        ( n) ＝
      coefficient-constant-formal-power-series-Commutative-Ring
        ( R)
        ( neg-Commutative-Ring R c)
        ( n)
    htpy-coefficients-neg-constant-formal-power-series-Commutative-Ring zero-ℕ =
      equational-reasoning
        neg-Commutative-Ring
          ( R)
          ( coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( constant-formal-power-series-Commutative-Ring R c)
            ( zero-ℕ))
        ＝ neg-Commutative-Ring R c
          by
            ap
              ( neg-Commutative-Ring R)
              ( eq-coefficient-constant-formal-power-series-Commutative-Ring
                ( R)
                ( c)
                ( zero-ℕ))
    htpy-coefficients-neg-constant-formal-power-series-Commutative-Ring
      (succ-ℕ n) =
      equational-reasoning
        neg-Commutative-Ring
          ( R)
          ( coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( constant-formal-power-series-Commutative-Ring R c)
            ( succ-ℕ n))
        ＝
          neg-Commutative-Ring R (zero-Commutative-Ring R)
          by
            ap
              ( neg-Commutative-Ring R)
              ( eq-coefficient-constant-formal-power-series-Commutative-Ring
                ( R)
                ( c)
                ( succ-ℕ n))
        ＝ zero-Commutative-Ring R by neg-zero-Commutative-Ring R

    neg-constant-formal-power-series-Commutative-Ring :
      neg-formal-power-series-Commutative-Ring
        ( R)
        ( constant-formal-power-series-Commutative-Ring R c) ＝
      constant-formal-power-series-Commutative-Ring R (neg-Commutative-Ring R c)
    neg-constant-formal-power-series-Commutative-Ring =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( coefficient-formal-power-series-coefficients-Commutative-Ring R _ ∙h
          htpy-coefficients-neg-constant-formal-power-series-Commutative-Ring ∙h
          inv-htpy
            ( coefficient-formal-power-series-coefficients-Commutative-Ring
              ( R)
              ( _)))
```

### Addition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  coefficient-add-formal-power-series-Commutative-Ring :
    (p q : formal-power-series-Commutative-Ring R) (n : ℕ) →
    type-Commutative-Ring R
  coefficient-add-formal-power-series-Commutative-Ring p q n =
    add-Commutative-Ring
      ( R)
      ( coefficient-formal-power-series-Commutative-Ring R p n)
      ( coefficient-formal-power-series-Commutative-Ring R q n)

  abstract
    add-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring R →
      formal-power-series-Commutative-Ring R →
      formal-power-series-Commutative-Ring R
    add-formal-power-series-Commutative-Ring p q =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( coefficient-add-formal-power-series-Commutative-Ring p q)

    eq-coefficient-add-formal-power-series-Commutative-Ring :
      (p q : formal-power-series-Commutative-Ring R) →
      coefficient-formal-power-series-Commutative-Ring
        ( R)
        ( add-formal-power-series-Commutative-Ring p q) ~
      coefficient-add-formal-power-series-Commutative-Ring p q
    eq-coefficient-add-formal-power-series-Commutative-Ring p q =
      coefficient-formal-power-series-coefficients-Commutative-Ring R _
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    commutative-add-formal-power-series-Commutative-Ring :
      (p q : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring R p q ＝
      add-formal-power-series-Commutative-Ring R q p
    commutative-add-formal-power-series-Commutative-Ring p q =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( λ n → equational-reasoning
          coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( add-formal-power-series-Commutative-Ring R p q)
            ( n)
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring R p n)
              ( coefficient-formal-power-series-Commutative-Ring R q n)
            by eq-coefficient-add-formal-power-series-Commutative-Ring R p q n
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring R q n)
              ( coefficient-formal-power-series-Commutative-Ring R p n)
            by commutative-add-Commutative-Ring R _ _
          ＝
            coefficient-formal-power-series-Commutative-Ring
              ( R)
              ( add-formal-power-series-Commutative-Ring R q p)
              ( n)
            by
              inv
                ( eq-coefficient-add-formal-power-series-Commutative-Ring
                  ( R)
                  ( q)
                  ( p)
                  ( n)))
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-unit-law-add-formal-power-series-Commutative-Ring :
      (p : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring
        ( R)
        ( zero-formal-power-series-Commutative-Ring R)
        ( p) ＝ p
    left-unit-law-add-formal-power-series-Commutative-Ring p =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( λ n → equational-reasoning
          coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( add-formal-power-series-Commutative-Ring
              ( R)
              ( zero-formal-power-series-Commutative-Ring R)
              ( p))
            ( n)
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( zero-formal-power-series-Commutative-Ring R)
                ( n))
              ( coefficient-formal-power-series-Commutative-Ring R p n)
            by eq-coefficient-add-formal-power-series-Commutative-Ring R _ _ n
          ＝
            add-Commutative-Ring
              ( R)
              ( zero-Commutative-Ring R)
              ( coefficient-formal-power-series-Commutative-Ring R p n)
            by
              ap
                ( λ c →
                  add-Commutative-Ring
                    ( R)
                    ( c)
                    ( coefficient-formal-power-series-Commutative-Ring R p n))
                ( is-zero-coefficient-zero-formal-power-series-Commutative-Ring
                  ( R)
                  ( n))
          ＝ coefficient-formal-power-series-Commutative-Ring R p n
            by left-unit-law-add-Commutative-Ring R _)

    right-unit-law-add-formal-power-series-Commutative-Ring :
      (p : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring
        ( R)
        ( p)
        ( zero-formal-power-series-Commutative-Ring R) ＝ p
    right-unit-law-add-formal-power-series-Commutative-Ring p =
      commutative-add-formal-power-series-Commutative-Ring R p _ ∙
      left-unit-law-add-formal-power-series-Commutative-Ring p
```

#### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
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
    associative-add-formal-power-series-Commutative-Ring p q r =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( λ n → equational-reasoning
          coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( add-formal-power-series-Commutative-Ring
              ( R)
              ( add-formal-power-series-Commutative-Ring R p q)
              ( r))
            ( n)
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( add-formal-power-series-Commutative-Ring R p q)
                ( n))
              ( coefficient-formal-power-series-Commutative-Ring R r n)
            by eq-coefficient-add-formal-power-series-Commutative-Ring R _ _ n
          ＝
            add-Commutative-Ring
              ( R)
              ( add-Commutative-Ring
                ( R)
                ( coefficient-formal-power-series-Commutative-Ring R p n)
                ( coefficient-formal-power-series-Commutative-Ring R q n))
              ( coefficient-formal-power-series-Commutative-Ring R r n)
            by
              ap
                ( add-Commutative-Ring' R _)
                ( eq-coefficient-add-formal-power-series-Commutative-Ring
                  ( R)
                  ( p)
                  ( q)
                  ( n))
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring R p n)
              ( add-Commutative-Ring
                ( R)
                ( coefficient-formal-power-series-Commutative-Ring R q n)
                ( coefficient-formal-power-series-Commutative-Ring R r n))
            by associative-add-Commutative-Ring R _ _ _
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring R p n)
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( add-formal-power-series-Commutative-Ring R q r)
                ( n))
            by
              ap
                ( add-Commutative-Ring R _)
                ( inv
                  ( eq-coefficient-add-formal-power-series-Commutative-Ring
                    ( R)
                    ( q)
                    ( r)
                    ( n)))
          ＝
            coefficient-formal-power-series-Commutative-Ring
              ( R)
              ( add-formal-power-series-Commutative-Ring
                ( R)
                ( p)
                ( add-formal-power-series-Commutative-Ring R q r))
              ( n)
            by
              inv
                ( eq-coefficient-add-formal-power-series-Commutative-Ring
                  ( R)
                  ( _)
                  ( _)
                  ( n)))
```

#### Inverse laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-inverse-law-add-formal-power-series-Commutative-Ring :
      (p : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring
        ( R)
        ( neg-formal-power-series-Commutative-Ring R p)
        ( p) ＝ zero-formal-power-series-Commutative-Ring R
    left-inverse-law-add-formal-power-series-Commutative-Ring p =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( λ n → equational-reasoning
          coefficient-formal-power-series-Commutative-Ring R
            (add-formal-power-series-Commutative-Ring
              ( R)
              ( neg-formal-power-series-Commutative-Ring R p)
              ( p))
            ( n)
          ＝
            add-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( neg-formal-power-series-Commutative-Ring R p)
                ( n))
              ( coefficient-formal-power-series-Commutative-Ring R p n)
            by eq-coefficient-add-formal-power-series-Commutative-Ring R _ _ n
          ＝
            add-Commutative-Ring
              ( R)
              ( neg-Commutative-Ring
                ( R)
                ( coefficient-formal-power-series-Commutative-Ring R p n))
              ( coefficient-formal-power-series-Commutative-Ring R p n)
            by
              ap
                ( add-Commutative-Ring' R _)
                ( eq-coefficient-neg-formal-power-series-Commutative-Ring R p n)
          ＝ zero-Commutative-Ring R
            by left-inverse-law-add-Commutative-Ring R _
          ＝
            coefficient-formal-power-series-Commutative-Ring
              ( R)
              ( zero-formal-power-series-Commutative-Ring R)
              ( n)
            by
              inv
                ( is-zero-coefficient-zero-formal-power-series-Commutative-Ring
                  ( R)
                  ( n)))

    right-inverse-law-add-formal-power-series-Commutative-Ring :
      (p : formal-power-series-Commutative-Ring R) →
      add-formal-power-series-Commutative-Ring
        ( R)
        ( p)
        ( neg-formal-power-series-Commutative-Ring R p) ＝
      zero-formal-power-series-Commutative-Ring R
    right-inverse-law-add-formal-power-series-Commutative-Ring p =
      commutative-add-formal-power-series-Commutative-Ring R _ _ ∙
      left-inverse-law-add-formal-power-series-Commutative-Ring p
```

#### The additive group of formal power series

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  semigroup-add-formal-power-series-Commutative-Ring : Semigroup l
  semigroup-add-formal-power-series-Commutative-Ring =
    set-formal-power-series-Commutative-Ring R ,
    add-formal-power-series-Commutative-Ring R ,
    associative-add-formal-power-series-Commutative-Ring R

  is-unital-add-formal-power-series-Commutative-Ring :
    is-unital (add-formal-power-series-Commutative-Ring R)
  is-unital-add-formal-power-series-Commutative-Ring =
    zero-formal-power-series-Commutative-Ring R ,
    left-unit-law-add-formal-power-series-Commutative-Ring R ,
    right-unit-law-add-formal-power-series-Commutative-Ring R

  monoid-add-formal-power-series-Commutative-Ring : Monoid l
  monoid-add-formal-power-series-Commutative-Ring =
    semigroup-add-formal-power-series-Commutative-Ring ,
    is-unital-add-formal-power-series-Commutative-Ring

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
  coefficient-mul-formal-power-series-Commutative-Ring n =
    sum-Commutative-Ring
      ( R)
      ( succ-ℕ n)
      ( λ k →
        mul-Commutative-Ring
          ( R)
          ( coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( p)
            ( nat-Fin (succ-ℕ n) k))
          ( coefficient-formal-power-series-Commutative-Ring
            ( R)
            ( q)
            ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k))))

  abstract
    mul-formal-power-series-Commutative-Ring :
      formal-power-series-Commutative-Ring R
    mul-formal-power-series-Commutative-Ring =
      formal-power-series-coefficients-Commutative-Ring
        ( R)
        ( coefficient-mul-formal-power-series-Commutative-Ring)

    eq-coefficient-mul-formal-power-series-Commutative-Ring :
      coefficient-formal-power-series-Commutative-Ring
        ( R)
        ( mul-formal-power-series-Commutative-Ring) ~
      coefficient-mul-formal-power-series-Commutative-Ring
    eq-coefficient-mul-formal-power-series-Commutative-Ring =
      coefficient-formal-power-series-coefficients-Commutative-Ring R _
```

#### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p q : formal-power-series-Commutative-Ring R)
  where

  abstract
    htpy-coefficients-commutative-mul-formal-power-series-Commutative-Ring :
      coefficient-mul-formal-power-series-Commutative-Ring R p q ~
      coefficient-mul-formal-power-series-Commutative-Ring R q p
    htpy-coefficients-commutative-mul-formal-power-series-Commutative-Ring n =
      preserves-sum-permutation-Commutative-Ring
        ( R)
        ( succ-ℕ n)
        ( equiv-involution (involution-opposite-Fin (succ-ℕ n)))
        ( λ k →
          mul-Commutative-Ring
            ( R)
            ( coefficient-formal-power-series-Commutative-Ring
              ( R)
              ( p)
              ( nat-Fin (succ-ℕ n) k))
            ( coefficient-formal-power-series-Commutative-Ring
              ( R)
              ( q)
              ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k)))) ∙
      htpy-sum-Commutative-Ring
        ( R)
        ( succ-ℕ n)
        ( λ k →
          ap
            ( λ m →
              mul-Commutative-Ring
                ( R)
                ( coefficient-formal-power-series-Commutative-Ring
                  ( R)
                  ( p)
                  ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k)))
                ( coefficient-formal-power-series-Commutative-Ring
                  ( R)
                  ( q)
                  ( nat-Fin (succ-ℕ n) m)))
            (is-involution-opposite-Fin (succ-ℕ n) k) ∙
          commutative-mul-Commutative-Ring R _ _)

    commutative-mul-formal-power-series-Commutative-Ring :
      mul-formal-power-series-Commutative-Ring R p q ＝
      mul-formal-power-series-Commutative-Ring R q p
    commutative-mul-formal-power-series-Commutative-Ring =
      eq-htpy-coefficients-formal-power-series-Commutative-Ring
        ( R)
        ( _)
        ( _)
        ( eq-coefficient-mul-formal-power-series-Commutative-Ring R p q ∙h
          htpy-coefficients-commutative-mul-formal-power-series-Commutative-Ring ∙h
          inv-htpy
            ( eq-coefficient-mul-formal-power-series-Commutative-Ring R q p))
```

#### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  (p : formal-power-series-Commutative-Ring R)
  where

  abstract
    htpy-coefficients-right-unit-law-mul-formal-power-series-Commutative-Ring :
      coefficient-mul-formal-power-series-Commutative-Ring
        ( R)
        ( p)
        ( one-formal-power-series-Commutative-Ring R) ~
      coefficient-formal-power-series-Commutative-Ring R p
    htpy-coefficients-right-unit-law-mul-formal-power-series-Commutative-Ring
      n =
      equational-reasoning
        sum-Commutative-Ring
          ( R)
          ( succ-ℕ n)
          ( λ k →
            mul-Commutative-Ring
              ( R)
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( p)
                ( nat-Fin (succ-ℕ n) k))
              ( coefficient-formal-power-series-Commutative-Ring
                ( R)
                ( one-formal-power-series-Commutative-Ring R)
                ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k))))
          ＝
            sum-Commutative-Ring
              ( R)
              ( succ-ℕ n)
              ( λ k →
                mul-Commutative-Ring
                  ( R)
                  ( coefficient-formal-power-series-Commutative-Ring
                    ( R)
                    ( p)
                    ( nat-Fin (succ-ℕ n) k))
                  ( coefficient-constant-formal-power-series-Commutative-Ring
                    ( R)
                    ( one-Commutative-Ring R)
                    ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k))))
            by
              htpy-sum-Commutative-Ring
                ( R)
                ( succ-ℕ n)
                ( λ k →
                  ap
                    ( mul-Commutative-Ring
                      ( R)
                      ( coefficient-formal-power-series-Commutative-Ring
                        ( R)
                        ( p)
                        ( nat-Fin (succ-ℕ n) k)))
                    ( eq-coefficient-constant-formal-power-series-Commutative-Ring
                      ( R)
                      ( one-Commutative-Ring R)
                      ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k))))
          ＝
            add-Commutative-Ring
              ( R)
              ( sum-Commutative-Ring
                ( R)
                ( n)
                ( λ k →
                  mul-Commutative-Ring
                    ( R)
                    ( coefficient-formal-power-series-Commutative-Ring
                      ( R)
                      ( p)
                      ( nat-Fin (succ-ℕ n) (inl-Fin n k)))
                    ( coefficient-constant-formal-power-series-Commutative-Ring
                      ( R)
                      ( one-Commutative-Ring R)
                      ( nat-Fin
                        ( succ-ℕ n)
                        ( opposite-Fin (succ-ℕ n) (inl-Fin n k))))))
              ( mul-Commutative-Ring
                ( R)
                ( coefficient-formal-power-series-Commutative-Ring R p n)
                ( coefficient-constant-formal-power-series-Commutative-Ring
                  ( R)
                  ( one-Commutative-Ring R)
                  ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) (inr star)))))
            by
              cons-sum-Commutative-Ring
                ( R)
                ( n)
                ( λ k →
                  mul-Commutative-Ring
                    ( R)
                    ( coefficient-formal-power-series-Commutative-Ring
                      ( R)
                      ( p)
                      ( nat-Fin (succ-ℕ n) k))
                    ( coefficient-constant-formal-power-series-Commutative-Ring
                      ( R)
                      ( one-Commutative-Ring R)
                      ( nat-Fin (succ-ℕ n) (opposite-Fin (succ-ℕ n) k))))
                ( refl)
          ＝ {!   !} by {!   !}

  -- left-unit-law-mul-formal-power-series-Commutative-Ring :
```
