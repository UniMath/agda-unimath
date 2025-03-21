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
      Im f
      ∧  \
     /    \
    /      ∨
  A ------> B
       f
```

## Definition

### Factorization operations

```agda
instance-factorization-operation :
  {l1 l2 : Level} (l3 : Level) (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
instance-factorization-operation l3 A B = (f : A → B) → factorization l3 f

factorization-operation : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
factorization-operation l1 l2 l3 =
  {A : UU l1} {B : UU l2} → instance-factorization-operation l3 A B
```
