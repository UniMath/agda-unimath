# Symmetric bilinear forms in real vector spaces

```agda
module linear-algebra.symmetric-bilinear-forms-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import linear-algebra.bilinear-forms-real-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

A [bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md) `B` on a
[real vector space](linear-algebra.real-vector-spaces.md) `V` is
{{#concept "symmetric" Agda=is-symmetric-bilinear-form-ℝ-Vector-Space Disambiguation="a bilinear form on a real vector space" WDID=Q2100018 WD="symmetric bilinear form"}}
if `B u v ＝ B v u` for all `u` and `v` in `V`.

## Definition

### Symmetry of a bilinear form

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (B : bilinear-form-ℝ-Vector-Space V)
  where

  is-symmetric-prop-bilinear-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-symmetric-prop-bilinear-form-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ y →
            Id-Prop
              ( ℝ-Set l1)
              ( map-bilinear-form-ℝ-Vector-Space V B x y)
              ( map-bilinear-form-ℝ-Vector-Space V B y x)))

  is-symmetric-bilinear-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-symmetric-bilinear-form-ℝ-Vector-Space =
    type-Prop is-symmetric-prop-bilinear-form-ℝ-Vector-Space
```

## External links

- [Symmetric bilinear form](https://en.wikipedia.org/wiki/Symmetric_bilinear_form)
  on Wikipedia
