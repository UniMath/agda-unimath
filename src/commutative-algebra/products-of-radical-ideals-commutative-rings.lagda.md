# Products of radical ideals in a commutative ring

```agda
module commutative-algebra.products-of-radical-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.products-of-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.universe-levels
```

</details>

## Idea

The **product** of two
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md) `I`
and `J` is the
[radical](commutative-algebra.radicals-of-ideals-commutative-rings.md) of the
[product](commutative-algebra.products-of-ideals-commutative-rings.md) if `I`
and `J`. In other words, the product of two radical ideals `I` and `J` is the
least radical ideal that contains the products of elements in `I` and in `J`.

## Definitions

### The universal property of the product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  contains-product-radical-ideal-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  contains-product-radical-ideal-Commutative-Ring K =
    contains-product-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)
      ( ideal-radical-ideal-Commutative-Ring A J)
      ( ideal-radical-ideal-Commutative-Ring A K)

  is-product-radical-ideal-Commutative-Ring :
    {l4 : Level} (K : radical-ideal-Commutative-Ring l4 A) →
    contains-product-radical-ideal-Commutative-Ring K → UUω
  is-product-radical-ideal-Commutative-Ring K H =
    {l5 : Level} (L : radical-ideal-Commutative-Ring l5 A) →
    contains-product-radical-ideal-Commutative-Ring L →
    leq-radical-ideal-Commutative-Ring A K L
```

### The product of two ideals in a commutative ring

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  (J : radical-ideal-Commutative-Ring l3 A)
  where

  generating-subset-product-radical-ideal-Commutative-Ring :
    subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  generating-subset-product-radical-ideal-Commutative-Ring =
    generating-subset-product-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)
      ( ideal-radical-ideal-Commutative-Ring A J)

  product-radical-ideal-Commutative-Ring :
    radical-ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-radical-ideal-Commutative-Ring =
    radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))

  ideal-product-radical-ideal-Commutative-Ring :
    ideal-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  ideal-product-radical-ideal-Commutative-Ring =
    ideal-radical-ideal-Commutative-Ring A
      product-radical-ideal-Commutative-Ring

  is-in-product-radical-ideal-Commutative-Ring :
    type-Commutative-Ring A → UU (l1 ⊔ l2 ⊔ l3)
  is-in-product-radical-ideal-Commutative-Ring =
    is-in-radical-ideal-Commutative-Ring A
      product-radical-ideal-Commutative-Ring

  contains-product-product-radical-ideal-Commutative-Ring :
    contains-product-radical-ideal-Commutative-Ring A I J
      product-radical-ideal-Commutative-Ring
  contains-product-product-radical-ideal-Commutative-Ring x y H K =
    contains-ideal-radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))
      ( mul-Commutative-Ring A x y)
      ( contains-product-product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J)
        ( x)
        ( y)
        ( H)
        ( K))

  is-product-radical-ideal-product-radical-ideal-Commutative-Ring :
    is-product-radical-ideal-Commutative-Ring A I J
      product-radical-ideal-Commutative-Ring
      contains-product-product-radical-ideal-Commutative-Ring
  is-product-radical-ideal-product-radical-ideal-Commutative-Ring K H =
    is-radical-of-ideal-radical-of-ideal-Commutative-Ring A
      ( product-ideal-Commutative-Ring A
        ( ideal-radical-ideal-Commutative-Ring A I)
        ( ideal-radical-ideal-Commutative-Ring A J))
      ( K)
      ( is-product-ideal-product-ideal-Commutative-Ring A
          ( ideal-radical-ideal-Commutative-Ring A I)
          ( ideal-radical-ideal-Commutative-Ring A J)
          ( ideal-radical-ideal-Commutative-Ring A K)
          ( H))
```
