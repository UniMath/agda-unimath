# The universal property of free vector spaces

```agda
module linear-algebra.universal-property-free-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.vector-spaces
open import commutative-algebra.heyting-fields
open import foundation.universe-levels
open import linear-algebra.isomorphisms-vector-spaces
open import linear-algebra.linear-maps-vector-spaces
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (G : UU l2)
  (V : Vector-Space l3 K)
  (in-V : G → type-Vector-Space K V)
  where

  is-free-
```
