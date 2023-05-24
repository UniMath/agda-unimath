# The Zariski locale

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module commutative-algebra.zariski-locale where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.joins-ideals-commutative-rings
open import commutative-algebra.joins-radical-ideals-commutative-rings
open import commutative-algebra.products-of-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.radicals-of-ideals-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

The **Zariski locale** of a
[commutative ring](commutative-algebra.commutative-rings.md) `A` is the
[large locale](order-theory.large-locales.md) consisting of
[radical ideals](commutative-algebra.radical-ideals-commutative-rings.md) of
`A`. Our proof of the fact that meets distribute over arbitrary joins uses the
fact that the intersection `I ∩ J` of radical ideals is equivalently described
as the radical ideal `√ IJ` of the
[product ideal](commutative-algebra.products-of-ideals-commutative-rings.md).

## Preliminary properties

### Products of radical ideals distribute over joins

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → radical-ideal-Commutative-Ring l4 A)
  where

  distributive-product-join-family-of-radical-ideals-Commutative-Ring :
    product-radical-ideal-Commutative-Ring A
      ( I)
      ( join-family-of-radical-ideals-Commutative-Ring A J) ＝
    join-family-of-radical-ideals-Commutative-Ring A
      ( λ α → product-radical-ideal-Commutative-Ring A I (J α))
  distributive-product-join-family-of-radical-ideals-Commutative-Ring =
    eq-has-same-elements-radical-ideal-Commutative-Ring A
      ( product-radical-ideal-Commutative-Ring A
        ( I)
        ( join-family-of-radical-ideals-Commutative-Ring A J))
      ( join-family-of-radical-ideals-Commutative-Ring A
        ( λ α → product-radical-ideal-Commutative-Ring A I (J α)))
      ( λ x →
        ( is-product-product-radical-ideal-Commutative-Ring A I
            ( join-family-of-radical-ideals-Commutative-Ring A J)
            ( join-family-of-radical-ideals-Commutative-Ring A
              ( λ α → product-radical-ideal-Commutative-Ring A I (J α)))
            ( λ r s p →
              {!!})
            ( x)) ,
        ( λ H →
          {!!}))
```

### Intersections of radical ideals distribute over joins

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Commutative-Ring l1)
  (I : radical-ideal-Commutative-Ring l2 A)
  {U : UU l3} (J : U → radical-ideal-Commutative-Ring l4 A)
  where
```

## Definition

### The Zariski locale
