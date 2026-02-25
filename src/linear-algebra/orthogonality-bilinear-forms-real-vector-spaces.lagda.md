# Orthogonality relative to a bilinear form in a real vector space

```agda
module linear-algebra.orthogonality-bilinear-forms-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.bilinear-forms-real-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

Two elements `u` and `v` of a
[real vector space](linear-algebra.real-vector-spaces.md) `V` are
{{#concept "orthogonal" Disambiguation="relative to a bilinear form over a real vector space" Agda=is-orthogonal-bilinear-form-ℝ-Vector-Space}}
relative to a
[bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md)
`B : V → V → ℝ` if `B u v = 0`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (B : bilinear-form-ℝ-Vector-Space V)
  where

  is-orthogonal-prop-bilinear-form-ℝ-Vector-Space :
    Relation-Prop l1 (type-ℝ-Vector-Space V)
  is-orthogonal-prop-bilinear-form-ℝ-Vector-Space v w =
    is-zero-prop-ℝ (map-bilinear-form-ℝ-Vector-Space V B v w)

  is-orthogonal-bilinear-form-ℝ-Vector-Space :
    Relation l1 (type-ℝ-Vector-Space V)
  is-orthogonal-bilinear-form-ℝ-Vector-Space =
    type-Relation-Prop is-orthogonal-prop-bilinear-form-ℝ-Vector-Space
```
