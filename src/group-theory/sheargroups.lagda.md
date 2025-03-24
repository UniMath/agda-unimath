# Sheargroups

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.sheargroups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels
```

</details>

## Definition

```agda
Sheargroup : (l : Level) → UU (lsuc l)
Sheargroup l =
  Σ ( Set l)
    ( λ X →
      Σ ( type-Set X)
        ( λ e →
          Σ (type-Set X → type-Set X → type-Set X)
            ( λ m →
              ( (x : type-Set X) → Id (m e x) x) ×
              ( ( (x : type-Set X) → Id (m x x) e) ×
                ( (x y z : type-Set X) →
                  Id (m x (m y z)) (m (m (m x (m y e)) e) z))))))
```
