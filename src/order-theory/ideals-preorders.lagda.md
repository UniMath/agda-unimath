# Ideals in preorders

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.ideals-preorders
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.inhabited-types funext univalence truncations
open import foundation.universe-levels

open import order-theory.lower-types-preorders funext univalence truncations
open import order-theory.preorders funext univalence truncations
```

</details>

## Idea

**Ideals** in preorders are inhabited lower types `L` that contain an upper
bound for every pair of elements in `L`.

## Definition

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  is-ideal-lower-type-Preorder :
    {l3 : Level} (L : lower-type-Preorder l3 P) → UU (l1 ⊔ l2 ⊔ l3)
  is-ideal-lower-type-Preorder L =
    ( is-inhabited (type-lower-type-Preorder P L)) ×
    ( (x y : type-lower-type-Preorder P L) →
      is-inhabited
        ( Σ ( type-lower-type-Preorder P L)
            ( λ z →
              ( leq-lower-type-Preorder P L x z) ×
              ( leq-lower-type-Preorder P L y z))))
```
