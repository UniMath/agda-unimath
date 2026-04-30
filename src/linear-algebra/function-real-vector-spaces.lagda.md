# Function real vector spaces

```agda
module linear-algebra.function-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.function-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

Given a type `X` and a [real vector space](linear-algebra.real-vector-spaces.md)
`V`, the functions `X → V` form a real vector space.

## Definition

```agda
function-ℝ-Vector-Space :
  {l1 l2 l3 : Level} (V : ℝ-Vector-Space l1 l2) → UU l3 →
  ℝ-Vector-Space l1 (l2 ⊔ l3)
function-ℝ-Vector-Space {l1 = l1} = function-Vector-Space (heyting-field-ℝ l1)
```

## Properties

### The functions `X → ℝ` form a real vector space

```agda
vector-space-function-ℝ :
  {l1 : Level} (l2 : Level) → UU l1 → ℝ-Vector-Space l2 (l1 ⊔ lsuc l2)
vector-space-function-ℝ l2 =
  function-vector-space-Heyting-Field (heyting-field-ℝ l2)
```
