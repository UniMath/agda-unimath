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

### The product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : ideal-Commutative-Ring l2 A) (J : ideal-Commutative-Ring l3 A)
  where

  generating-subset-product-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  generating-subset-product-ideal-Commutative-Ring =
    generating-subset-product-ideal-Ring
      ( ring-Commutative-Ring A)
      ( I)
      ( J)

  product-ideal-Commutative-Ring : ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-ideal-Commutative-Ring =
    product-ideal-Ring (ring-Commutative-Ring A) I J
```
