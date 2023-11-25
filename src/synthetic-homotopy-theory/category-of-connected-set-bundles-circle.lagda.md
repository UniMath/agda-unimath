# The category of connected set bundles over the circle

```agda
module synthetic-homotopy-theory.category-of-connected-set-bundles-circle where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subcategories
open import category-theory.large-categories

open import foundation.category-of-families-of-sets
open import foundation.universe-levels

open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.connected-set-bundles-circle
```

</details>

## Idea

The
[connected set bundles over the circle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
form a [large category](category-theory.large-categories.md). This large
category is the categorification of the [poset](order-theory.posets.md) of the
[natural numbers ordered by divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

## Definitions

### The category of connected set bundles over the circle

```agda
connected-set-bundle-𝕊¹-Large-Category :
  Large-Category (λ l → lzero ⊔ lsuc l) (λ l1 l2 → l1 ⊔ l2)
connected-set-bundle-𝕊¹-Large-Category =
  large-category-Full-Large-Subcategory
    ( Family-Of-Sets-Large-Category 𝕊¹)
    ( is-connected-prop-set-bundle-𝕊¹)
```
