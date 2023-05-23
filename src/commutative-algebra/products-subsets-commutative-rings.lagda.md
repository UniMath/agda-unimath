# Products of subsets in commutative rings

```agda
module commutative-algebra.products-subsets-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The **product** of two [subsets](commutative-algebra.subsets-commutative-rings.md) `S` and `T` of a [commutative ring](commutative-algebra.commutative-rings.md) `A` is the subset consistng of products `xy` where `x ∈ S` and `y ∈ T`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A) (T : subset-Commutative-Ring l3 A)
  where

  product-subset-Commutative-Ring : subset-Commutative-Ring (l1 ⊔ l2 ⊔ l3) A
  product-subset-Commutative-Ring x =
    trunc-Prop
      ( Σ ( type-subtype S)
          ( λ s →
            Σ ( type-subtype T)
              ( λ t → x ＝ mul-Commutative-Ring A (pr1 s) (pr1 t))))
```
