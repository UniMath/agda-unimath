# Product decompositions

```agda
module foundation.product-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
```

</details>

## Definitions

### Binary product decomposition

```agda
module _
  {l1 : Level} (l2 l3 : Level) (X : UU l1)
  where

  binary-product-Decomposition : UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  binary-product-Decomposition =
    Σ (UU l2) (λ A → Σ (UU l3) (λ B → X ≃ (A × B)))

module _
  {l1 l2 l3 : Level} {X : UU l1}
  (d : binary-product-Decomposition l2 l3 X)
  where

  left-summand-binary-product-Decomposition : UU l2
  left-summand-binary-product-Decomposition = pr1 d

  right-summand-binary-product-Decomposition : UU l3
  right-summand-binary-product-Decomposition = pr1 (pr2 d)

  matching-correspondence-binary-product-Decomposition :
    X ≃
    ( left-summand-binary-product-Decomposition ×
      right-summand-binary-product-Decomposition)
  matching-correspondence-binary-product-Decomposition = pr2 (pr2 d)
```
