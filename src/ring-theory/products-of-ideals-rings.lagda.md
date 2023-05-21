# Products of ideals in rings

```agda
module ring-theory.products-of-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import ring-theory.ideals-generated-by-subsets-rings
open import ring-theory.ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The **product** of two [ideals](ring-theory.ideals-rings.md) `I` and `J` in a
[ring](ring-theory.rings.md) is the ideal generated all products of elements in
`I` and `J`.

## Definition

### The product of two ideals in a ring

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R) (J : ideal-Ring l3 R)
  where

  generating-subset-product-ideal-Ring : subset-Ring (l1 ⊔ l2 ⊔ l3) R
  generating-subset-product-ideal-Ring r =
    trunc-Prop
      ( Σ ( type-ideal-Ring R I)
          ( λ x →
            Σ ( type-ideal-Ring R J)
              ( λ y →
                mul-Ring R
                  ( inclusion-ideal-Ring R I x)
                  ( inclusion-ideal-Ring R J y) ＝ r)))

  product-ideal-Ring : ideal-Ring (l1 ⊔ l2 ⊔ l3) R
  product-ideal-Ring = ideal-subset-Ring R generating-subset-product-ideal-Ring
```
