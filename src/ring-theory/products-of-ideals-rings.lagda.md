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
open import ring-theory.posets-of-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

The **product** of two [ideals](ring-theory.ideals-rings.md) `I` and `J` in a
[ring](ring-theory.rings.md) is the ideal generated all products of elements in
`I` and `J`.

## Definition

### The universal property of the product of two ideals in a ring

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (I : ideal-Ring l2 R) (J : ideal-Ring l3 R)
  where

  contains-product-ideal-Ring :
    {l4 : Level} (K : ideal-Ring l4 R) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  contains-product-ideal-Ring K =
    (x y : type-Ring R) →
    is-in-ideal-Ring R I x → is-in-ideal-Ring R J y →
    is-in-ideal-Ring R K (mul-Ring R x y)

  is-product-ideal-Ring :
    {l4 : Level} (K : ideal-Ring l4 R) → contains-product-ideal-Ring K → UUω
  is-product-ideal-Ring K H =
    {l5 : Level} (L : ideal-Ring l5 R) →
    contains-product-ideal-Ring L → leq-ideal-Ring R K L
```

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

  subset-product-ideal-Ring : subset-Ring (l1 ⊔ l2 ⊔ l3) R
  subset-product-ideal-Ring = subset-ideal-Ring R product-ideal-Ring

  is-in-product-ideal-Ring : type-Ring R → UU (l1 ⊔ l2 ⊔ l3)
  is-in-product-ideal-Ring = is-in-ideal-Ring R product-ideal-Ring

  contains-product-product-ideal-Ring :
    (x y : type-Ring R) →
    is-in-ideal-Ring R I x → is-in-ideal-Ring R J y →
    is-in-product-ideal-Ring (mul-Ring R x y)
  contains-product-product-ideal-Ring x y H K =
    contains-subset-ideal-subset-Ring R
      ( generating-subset-product-ideal-Ring)
      ( mul-Ring R x y)
      ( unit-trunc-Prop ((x , H) , (y , K) , refl))

  is-product-ideal-product-ideal-Ring :
    is-product-ideal-Ring R I J
      ( product-ideal-Ring)
      ( contains-product-product-ideal-Ring)
  is-product-ideal-product-ideal-Ring K H =
    is-ideal-generated-by-subset-ideal-subset-Ring R
      ( generating-subset-product-ideal-Ring)
      ( K)
      ( λ x p →
        apply-universal-property-trunc-Prop p
          ( subset-ideal-Ring R K x)
          ( λ ((r , p) , ((s , q) , z)) →
            is-closed-under-eq-ideal-Ring R K (H r s p q) z))
```
