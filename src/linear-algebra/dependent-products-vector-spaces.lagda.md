# Dependent products of vector spaces

```agda
module linear-algebra.dependent-products-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.dependent-products-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

Given a [Heyting field](commutative-algebra.heyting-fields.md) `K` and a family
of [vector spaces](linear-algebra.vector-spaces.md) `Vᵢ` over `K` indexed by
`i : I`, the dependent product `Πᵢ Vᵢ` is a vector space over `K`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (K : Heyting-Field l1)
  (I : UU l2)
  (V : I → Vector-Space l3 K)
  where

  Π-Vector-Space : Vector-Space (l2 ⊔ l3) K
  Π-Vector-Space = Π-left-module-Ring (ring-Heyting-Field K) I V
```
