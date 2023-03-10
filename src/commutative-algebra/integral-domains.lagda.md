# Integral domains

```agda
module commutative-algebra.integral-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import ring-theory.rings
```

</details>

## Idea

An integral domain is a commutative ring `R` such that the product of any two nonzero elements in `R` is nonzero. Equivalently, a commutative ring `R` is an integral domain if and only if multiplication by any nonzero element `a` satisfies the cancellation property: `ax = ay ⇒ x = y`.

## Definition

### The cancellation property for a commutative ring

```agda
cancellation-property-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → UU l
cancellation-property-Commutative-Ring R =
  (x : type-Commutative-Ring R) → is-nonzero-Commutative-Ring R x →
  is-injective (mul-Commutative-Ring R x)
```

### Integral domains

```agda
Integral-Domain : (l : Level) → UU (lsuc l)
Integral-Domain l =
  Σ (Commutative-Ring l) cancellation-property-Commutative-Ring

module _
  {l : Level} (R : Integral-Domain l)
  where

  commutative-ring-Integral-Domain : Commutative-Ring l
  commutative-ring-Integral-Domain = pr1 R

  ring-Integral-Domain : Ring l
  ring-Integral-Domain = ring-Commutative-Ring commutative-ring-Integral-Domain

  set-Integral-Domain : Set l
  set-Integral-Domain = set-Ring ring-Integral-Domain

  type-Integral-Domain : UU l
  type-Integral-Domain = type-Ring ring-Integral-Domain

  is-set-type-Integral-Domain : is-set type-Integral-Domain
  is-set-type-Integral-Domain = is-set-type-Ring ring-Integral-Domain

  add-Integral-Domain : (x y : type-Integral-Domain) → type-Integral-Domain
  add-Integral-Domain = add-Ring ring-Integral-Domain

  zero-Integral-Domain : type-Integral-Domain
  zero-Integral-Domain = zero-Ring ring-Integral-Domain

  neg-Integral-Domain : type-Integral-Domain → type-Integral-Domain
  neg-Integral-Domain = neg-Ring ring-Integral-Domain

  mul-Integral-Domain : (x y : type-Integral-Domain) → type-Integral-Domain
  mul-Integral-Domain = mul-Ring ring-Integral-Domain

  one-Integral-Domain : type-Integral-Domain
  one-Integral-Domain = one-Ring ring-Integral-Domain
```
