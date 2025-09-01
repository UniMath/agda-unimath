# Furstenberg groups

```agda
module group-theory.furstenberg-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Definition

```agda
Furstenberg-Group : (l : Level) → UU (lsuc l)
Furstenberg-Group l =
  Σ ( Set l)
    ( λ X →
      ( type-trunc-Prop (type-Set X)) ×
      ( Σ ( type-Set X → type-Set X → type-Set X)
          ( λ μ →
            ( (x y z : type-Set X) → μ (μ x z) (μ y z) ＝ μ x y) ×
            ( Σ ( type-Set X → type-Set X → type-Set X)
                ( λ δ → (x y : type-Set X) → μ x (δ x y) ＝ y)))))
```
