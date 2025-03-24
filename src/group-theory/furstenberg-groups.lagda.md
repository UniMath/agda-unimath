# Furstenberg groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.furstenberg-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.propositional-truncations funext univalence
open import foundation.sets funext univalence
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
            ( (x y z : type-Set X) → Id (μ (μ x z) (μ y z)) (μ x y)) ×
            ( Σ ( type-Set X → type-Set X → type-Set X)
                ( λ δ → (x y : type-Set X) → Id (μ x (δ x y)) y)))))
```
