# Separated types

```agda
module orthogonal-factorization-systems.separated-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
```

</details>

## Idea

A type `A` is said to be **separated** with respect to a map `f`, or
**`f`-separated** if its identity types are `f`-local.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) (A : UU l3)
  where

  is-separated : UU (l1 ⊔ l2 ⊔ l3)
  is-separated = (x y : A) → is-local f (x ＝ y)
```
