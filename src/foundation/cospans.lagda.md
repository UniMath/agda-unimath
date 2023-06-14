# Cospans

```agda
module foundation.cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Definition

### Cospans

A cospan is a pair of functions with a common codomain

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
cospan l A B =
  Σ (UU l) (λ X → (A → X) × (B → X))
```
