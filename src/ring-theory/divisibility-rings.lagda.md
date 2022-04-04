# Divisibility in rings

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.divisibility-rings where

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.rings
```

## Idea

An element `d` in a ring `R` is said to divide `x : R` if there exists an element `y : R` such that `dy = x`.

## Definitions

```agda
module _
  {l : Level} (R : Ring l)
  where
  
  div-Ring : type-Ring R → type-Ring R → UU l
  div-Ring d x = Σ (type-Ring R) (λ y → Id (mul-Ring R d y) x)

  quotient-div-Ring : (d x : type-Ring R) → div-Ring d x → type-Ring R
  quotient-div-Ring d x = pr1

  eq-div-Ring :
    (d x : type-Ring R) (H : div-Ring d x) →
    Id (mul-Ring R d (quotient-div-Ring d x H)) x
  eq-div-Ring d x = pr2
```

## Properties

### The divisibility relation on a ring is reflexive

```agda
module _
  {l : Level} (R : Ring l)
  where

  refl-div-Ring : {x : type-Ring R} → div-Ring R x x
  pr1 refl-div-Ring = one-Ring R
  pr2 refl-div-Ring = right-unit-law-mul-Ring R _
```

### The divisibility relation on a ring is transitive

```agda
module _
  {l : Level} (R : Ring l)
  where

  transitive-div-Ring :
    {x y z : type-Ring R} → div-Ring R x y → div-Ring R y z → div-Ring R x z
  pr1 (transitive-div-Ring (pair u p) (pair v q)) = mul-Ring R u v
  pr2 (transitive-div-Ring (pair u p) (pair v q)) =
    ( inv (associative-mul-Ring R _ u v)) ∙
    ( (ap (mul-Ring' R v) p) ∙ q)
```

### Any element in a ring divides zero

```agda
module _
  {l : Level} (R : Ring l)
  where

  div-zero-Ring :
    {x : type-Ring R} → div-Ring R x (zero-Ring R)
  pr1 (div-zero-Ring {x}) = zero-Ring R
  pr2 (div-zero-Ring {x}) = right-zero-law-mul-Ring R x
```

### The only element of which zero is a divisor is zero itself

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-zero-div-zero-Ring :
    {x : type-Ring R} → div-Ring R (zero-Ring R) x → is-zero-Ring R x
  is-zero-div-zero-Ring (pair y p) = inv p ∙ left-zero-law-mul-Ring R y
```

### The unit of a ring divides any element

```agda
module _
  {l : Level} (R : Ring l)
  where

  div-one-Ring :
    {x : type-Ring R} → div-Ring R (one-Ring R) x
  pr1 (div-one-Ring {x}) = x
  pr2 (div-one-Ring {x}) = left-unit-law-mul-Ring R x
```
