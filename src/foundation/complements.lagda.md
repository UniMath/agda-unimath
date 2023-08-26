# Complements of type families

```agda
module foundation.complements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.function-types
```

</details>

## Idea

The **complement** of a type family `B` over `A` consists of the type of points
in `A` at which `B x` is [empty](foundation-core.empty-types.md).

```agda
complement :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
complement {l1} {l2} {A} B = Σ A (is-empty ∘ B)
```
