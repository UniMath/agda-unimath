# Factorization operations

```agda
module orthogonal-factorization-systems.factorization-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorizations-of-maps
```

</details>

## Idea

A **factorization operation** on a function type `A → B` is a choice of
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md) for
every map `f` in `A → B`.

```text
       ∙
      ^ \
     /   \
    /     v
  A -----> B
      f
```

## Definition

### Factorization operations

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  factorization-operation : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  factorization-operation l3 = (f : A → B) → factorization l3 f
```
