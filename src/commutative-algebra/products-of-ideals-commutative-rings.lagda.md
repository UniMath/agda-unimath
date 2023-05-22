# Products of ideals in commutative rings

```agda
module commutative-algebra.products-of-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.universe-levels

open import ring-theory.products-of-ideals-rings
```

</details>

## Idea

The **product** of two [ideals](commutative-algebra.ideals-commutative-rings.md)
`I` and `J` in a [commutative ring](commutative-algebra.commutative-rings.md) is
the ideal generated all products of elements in `I` and `J`.

## Definition

### The universal property of the product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 R) (J : ideal-Commutative-Ring l3 R)
  where

  contains-product-ideal-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 R) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  contains-product-ideal-Commutative-Ring =
    contains-product-ideal-Ring (ring-Commutative-Ring R) I J

  is-product-ideal-Commutative-Ring :
    {l4 : Level} (K : ideal-Commutative-Ring l4 R) →
    contains-product-ideal-Commutative-Ring K → UUω
  is-product-ideal-Commutative-Ring =
    is-product-ideal-Ring (ring-Commutative-Ring R) I J
```

### The product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  generating-subset-product-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  generating-subset-product-ideal-Commutative-Ring =
    generating-subset-product-ideal-Ring (ring-Commutative-Ring A) I J

  product-ideal-Commutative-Ring : ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-ideal-Commutative-Ring =
    product-ideal-Ring (ring-Commutative-Ring A) I J

  is-in-product-ideal-Commutative-Ring :
    type-Commutative-Ring A → UU (l1 ⊔ l2 ⊔ l3)
  is-in-product-ideal-Commutative-Ring =
    is-in-ideal-Commutative-Ring A product-ideal-Commutative-Ring

  contains-product-product-ideal-Commutative-Ring :
    contains-product-ideal-Commutative-Ring A I J product-ideal-Commutative-Ring
  contains-product-product-ideal-Commutative-Ring =
    contains-product-product-ideal-Ring (ring-Commutative-Ring A) I J

  is-product-ideal-product-ideal-Commutative-Ring :
    is-product-ideal-Commutative-Ring A I J
      product-ideal-Commutative-Ring
      contains-product-product-ideal-Commutative-Ring
  is-product-ideal-product-ideal-Commutative-Ring =
    is-product-ideal-product-ideal-Ring (ring-Commutative-Ring A) I J
```
