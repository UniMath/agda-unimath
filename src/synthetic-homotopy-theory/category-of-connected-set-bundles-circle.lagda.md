# The category of connected set bundles over the circle

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.category-of-connected-set-bundles-circle
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subcategories funext univalence truncations
open import category-theory.large-categories funext univalence truncations

open import foundation.category-of-families-of-sets funext univalence truncations
open import foundation.universe-levels

open import synthetic-homotopy-theory.circle funext univalence truncations
open import synthetic-homotopy-theory.connected-set-bundles-circle funext univalence truncations
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
connected-set-bundle-𝕊¹-Large-Category : Large-Category (lsuc) (_⊔_)
connected-set-bundle-𝕊¹-Large-Category =
  large-category-Full-Large-Subcategory
    ( Family-Of-Sets-Large-Category 𝕊¹)
    ( is-connected-prop-set-bundle-𝕊¹)
```
