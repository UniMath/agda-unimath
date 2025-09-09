# Polynomials in commutative rings

```agda
{-# OPTIONS --lossy-unification #-}

module commutative-algebra.polynomials-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.formal-power-series-commutative-rings
open import commutative-algebra.polynomials-commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.subgroups-abelian-groups

open import lists.sequences

open import logic.functoriality-existential-quantification

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "polynomial" WDID=Q43260 WD="polynomial" disambiguation="in a commutative ring" Agda=polynomial-Commutative-Ring}}
in a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[polynomial](commutative-algebra.polynomials-commutative-semirings.md) in `R`
interpreted as a
[commutative semiring](commutative-algebra.commutative-semirings.md).

## Definition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  is-polynomial-prop-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R → Prop l
  is-polynomial-prop-formal-power-series-Commutative-Ring =
    is-polynomial-prop-formal-power-series-Commutative-Semiring

  is-polynomial-formal-power-series-Commutative-Ring :
    formal-power-series-Commutative-Ring R → UU l
  is-polynomial-formal-power-series-Commutative-Ring =
    is-polynomial-formal-power-series-Commutative-Semiring

  polynomial-Commutative-Ring : UU l
  polynomial-Commutative-Ring =
    polynomial-Commutative-Semiring (commutative-semiring-Commutative-Ring R)

  formal-power-series-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring → formal-power-series-Commutative-Ring R
  formal-power-series-polynomial-Commutative-Ring =
    formal-power-series-polynomial-Commutative-Semiring

  coefficient-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring → sequence (type-Commutative-Ring R)
  coefficient-polynomial-Commutative-Ring =
    coefficient-polynomial-Commutative-Semiring

  is-polynomial-formal-power-series-polynomial-Commutative-Ring :
    (p : polynomial-Commutative-Ring) →
    is-polynomial-formal-power-series-Commutative-Ring
      ( formal-power-series-polynomial-Commutative-Ring p)
  is-polynomial-formal-power-series-polynomial-Commutative-Ring =
    is-polynomial-formal-power-series-polynomial-Commutative-Semiring
```

## Properties

### The constant zero polynomial

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  zero-polynomial-Commutative-Ring : polynomial-Commutative-Ring R
  zero-polynomial-Commutative-Ring = zero-polynomial-Commutative-Semiring _
```

### The constant one polynomial

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  one-polynomial-Commutative-Ring : polynomial-Commutative-Ring R
  one-polynomial-Commutative-Ring = one-polynomial-Commutative-Semiring _
```

### The identity polynomial

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  id-polynomial-Commutative-Ring : polynomial-Commutative-Ring R
  id-polynomial-Commutative-Ring = id-polynomial-Commutative-Semiring _
```

### The set of polynomials

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  set-polynomial-Commutative-Ring : Set l
  set-polynomial-Commutative-Ring =
    set-polynomial-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

### Evaluation of polynomials

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  ev-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring R → type-Commutative-Ring R →
    type-Commutative-Ring R
  ev-polynomial-Commutative-Ring = ev-polynomial-Commutative-Semiring
```

### Truncation of a formal power series into a polynomial

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  truncate-formal-power-series-Commutative-Ring :
    (n : ℕ) → formal-power-series-Commutative-Ring R →
    polynomial-Commutative-Ring R
  truncate-formal-power-series-Commutative-Ring =
    truncate-formal-power-series-Commutative-Semiring
```

### Addition of polynomials

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring R → polynomial-Commutative-Ring R →
    polynomial-Commutative-Ring R
  add-polynomial-Commutative-Ring = add-polynomial-Commutative-Semiring
```

#### The sum of two polynomials, evaluated at `x`, is equal to the sum of each polynomial evaluated at `x`

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  interchange-ev-add-polynomial-Commutative-Ring :
    (p q : polynomial-Commutative-Ring R) →
    (x : type-Commutative-Ring R) →
    ev-polynomial-Commutative-Ring R
      ( add-polynomial-Commutative-Ring R p q)
      ( x) ＝
    add-Commutative-Ring R
      ( ev-polynomial-Commutative-Ring R p x)
      ( ev-polynomial-Commutative-Ring R q x)
  interchange-ev-add-polynomial-Commutative-Ring =
    interchange-ev-add-polynomial-Commutative-Semiring
```

### Negation of polynomials

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    is-polynomial-neg-polynomial-Commutative-Ring :
      (p : polynomial-Commutative-Ring R) →
      is-polynomial-formal-power-series-Commutative-Ring R
        ( neg-formal-power-series-Commutative-Ring R
          ( formal-power-series-polynomial-Commutative-Ring R p))
    is-polynomial-neg-polynomial-Commutative-Ring (p , is-poly-p) =
      map-tot-exists
        ( λ n n≤k→pk=0 k n≤k →
          ap (neg-Commutative-Ring R) (n≤k→pk=0 k n≤k) ∙
          neg-zero-Ab (ab-Commutative-Ring R))
        ( is-poly-p)

  neg-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring R → polynomial-Commutative-Ring R
  neg-polynomial-Commutative-Ring (p , is-poly-p) =
    ( neg-formal-power-series-Commutative-Ring R p ,
      is-polynomial-neg-polynomial-Commutative-Ring (p , is-poly-p))
```

### The additive abelian group of polynomials in commutative rings

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  ab-polynomial-Commutative-Ring : Ab l
  ab-polynomial-Commutative-Ring =
    ab-Subgroup-Ab
      ( additive-ab-formal-power-series-Commutative-Ring R)
      ( is-polynomial-prop-formal-power-series-Commutative-Ring R ,
        is-polynomial-formal-power-series-polynomial-Commutative-Ring R
          ( zero-polynomial-Commutative-Ring R) ,
        ( λ {p} {q} is-poly-p is-poly-q →
          is-polynomial-add-polynomial-Commutative-Semiring
            ( p , is-poly-p)
            ( q , is-poly-q)) ,
        ( λ {p} is-poly-p →
          is-polynomial-neg-polynomial-Commutative-Ring R (p , is-poly-p)))
```

### Multiplication

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  mul-polynomial-Commutative-Ring :
    polynomial-Commutative-Ring R → polynomial-Commutative-Ring R →
    polynomial-Commutative-Ring R
  mul-polynomial-Commutative-Ring = mul-polynomial-Commutative-Semiring
```

### The commutative ring of polynomials

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  ring-polynomial-Commutative-Ring : Ring l
  ring-polynomial-Commutative-Ring =
    ( ab-polynomial-Commutative-Ring R ,
      pr1
        ( pr2
          ( semiring-polynomial-Commutative-Semiring
            ( commutative-semiring-Commutative-Ring R))))
```
