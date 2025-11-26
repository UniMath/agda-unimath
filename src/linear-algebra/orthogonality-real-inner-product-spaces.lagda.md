# Orthogonality in real inner product spaces

```agda
module linear-algebra.orthogonality-real-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.orthogonality-bilinear-forms-real-vector-spaces
open import linear-algebra.real-inner-product-spaces

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

Two vectors are
{{#concept "orthogonal" WDID=Q215067 WD="orthogonality" Agda=are-orthogonal-ℝ-Inner-Product-Space  Disambiguation="in a real inner product space"}}
in a [real inner product space](linear-algebra.real-inner-product-spaces.md) if
they are
[orthogonal](linear-algebra.orthogonality-bilinear-forms-real-vector-spaces.md)
relative to the inner product as a
[bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  are-orthogonal-prop-ℝ-Inner-Product-Space :
    Relation-Prop (lsuc l1) (type-ℝ-Inner-Product-Space V)
  are-orthogonal-prop-ℝ-Inner-Product-Space =
    are-orthogonal-prop-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space V)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space V)

  are-orthogonal-ℝ-Inner-Product-Space :
    Relation (lsuc l1) (type-ℝ-Inner-Product-Space V)
  are-orthogonal-ℝ-Inner-Product-Space =
    type-Relation-Prop are-orthogonal-prop-ℝ-Inner-Product-Space
```

## Properties

### The Pythagorean Theorem

The Pythagorean theorem for real inner product spaces asserts that for
orthogonal `v` and `w`, the squared norm of `v + w` is the sum of the squared
norm of `v` and the squared norm of `w`.

The Pythagorean theorem is the [4th](literature.100-theorems.md#4) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Proof

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    pythagorean-theorem-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      is-orthogonal-ℝ-Inner-Product-Space V v w →
      squared-norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V v w) ＝
      squared-norm-ℝ-Inner-Product-Space V v +ℝ
      squared-norm-ℝ-Inner-Product-Space V w
    pythagorean-theorem-ℝ-Inner-Product-Space v w v∙w=0 =
      let
        ⟨_,V_⟩ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          ⟨ v +V w ,V v +V w ⟩
          ＝ ⟨ v ,V v ⟩ +ℝ real-ℕ 2 *ℝ ⟨ v ,V w ⟩ +ℝ ⟨ w ,V w ⟩
            by squared-norm-add-ℝ-Inner-Product-Space V v w
          ＝ ⟨ v ,V v ⟩ +ℝ real-ℕ 2 *ℝ raise-ℝ l1 zero-ℝ +ℝ ⟨ w ,V w ⟩
            by ap-add-ℝ (ap-add-ℝ refl (ap-mul-ℝ refl v∙w=0)) refl
          ＝ ⟨ v ,V v ⟩ +ℝ zero-ℝ +ℝ ⟨ w ,V w ⟩
            by
              ap-add-ℝ
                ( eq-sim-ℝ
                  ( preserves-sim-left-add-ℝ _ _ _
                    ( similarity-reasoning-ℝ
                      real-ℕ 2 *ℝ raise-ℝ l1 zero-ℝ
                      ~ℝ real-ℕ 2 *ℝ zero-ℝ
                        by
                          preserves-sim-left-mul-ℝ _ _ _
                            ( sim-raise-ℝ' l1 zero-ℝ)
                      ~ℝ zero-ℝ
                        by right-zero-law-mul-ℝ _)))
                ( refl)
          ＝ ⟨ v ,V v ⟩ +ℝ ⟨ w ,V w ⟩
            by ap-add-ℝ (right-unit-law-add-ℝ _) refl

    norm-add-orthogonal-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      is-orthogonal-ℝ-Inner-Product-Space V v w →
      norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V v w) ＝
      real-sqrt-ℝ⁰⁺
        ( nonnegative-squared-norm-ℝ-Inner-Product-Space V v +ℝ⁰⁺
          nonnegative-squared-norm-ℝ-Inner-Product-Space V w)
    norm-add-orthogonal-ℝ-Inner-Product-Space v w v∙w=0 =
      ap
        ( real-sqrt-ℝ⁰⁺)
        ( eq-ℝ⁰⁺ _ _
          ( pythagorean-theorem-ℝ-Inner-Product-Space v w v∙w=0))
```

## References

{{#bibliography}}
