# Function vector spaces

```agda
module linear-algebra.function-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.function-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

Given a type `X` and a [vector space](linear-algebra.vector-spaces.md) `V` over
a [Heyting field](commutative-algebra.heyting-fields.md) `K`, the functions
`X → V` form a vector space over `K`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  (X : UU l3)
  where

  function-Vector-Space : Vector-Space (l2 ⊔ l3) K
  function-Vector-Space = function-left-module-Ring (ring-Heyting-Field K) V X
```

## Properties

### The functions `X → K` form a vector space over `K`

```agda
function-vector-space-Heyting-Field :
  {l1 l2 : Level} (K : Heyting-Field l1) → UU l2 → Vector-Space (l1 ⊔ l2) K
function-vector-space-Heyting-Field K =
  function-left-module-ring-Ring (ring-Heyting-Field K)
```
