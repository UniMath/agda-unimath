# Dependent products of real vector spaces

```agda
module linear-algebra.dependent-products-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import linear-algebra.dependent-products-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

Given a family of [real vector spaces](linear-algebra.real-vector-spaces.md)
`Vᵢ` indexed by `i : I`, the dependent product `Πᵢ Vᵢ` is a real vector space.

## Definition

```agda
Π-ℝ-Vector-Space :
  {l1 l2 l3 : Level} (I : UU l1) (V : I → ℝ-Vector-Space l2 l3) →
  ℝ-Vector-Space l2 (l1 ⊔ l3)
Π-ℝ-Vector-Space {l2 = l2} =
  Π-Vector-Space (heyting-field-ℝ l2)
```
