# Large function semigroups

```agda
module group-theory.large-function-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels

open import group-theory.large-semigroups
```

</details>

## Idea

Given a [large semigroup](group-theory.large-semigroups.md) `G` and an arbitrary
type `A`, `A → G` forms a large semigroup.

## Definition

```agda
function-Large-Semigroup :
  {l : Level} {α : Level → Level} → UU l → Large-Semigroup α →
  Large-Semigroup (λ l' → l ⊔ α l')
function-Large-Semigroup A G =
  make-Large-Semigroup
    ( λ l → function-Set A (set-Large-Semigroup G l))
    ( λ f g a → mul-Large-Semigroup G (f a) (g a))
    ( λ f g h →
      eq-htpy (λ a → associative-mul-Large-Semigroup G (f a) (g a) (h a)))
```
