# Sheargroups

```agda
module group-theory.sheargroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
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
              ( (x : type-Set X) → m e x ＝ x) ×
              ( ( (x : type-Set X) → m x x ＝ e) ×
                ( (x y z : type-Set X) →
                  m x (m y z) ＝ m (m (m x (m y e)) e) z)))))
```
