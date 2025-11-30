# Bilinear forms in real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.bilinear-forms-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.real-vector-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.multiplication-real-numbers
```

</details>

## Idea

A
{{#concept "bilinear form" WDID=Q837924 WD="bilinear form" Disambiguation="on a real vector space" Agda=bilinear-form-ℝ-Vector-Space}}
on a [real vector space](linear-algebra.real-vector-spaces.md) `V` is a map
`B : V → V → ℝ` that is linear in each argument:
`B (a * x + b * y) z = a * B x z + b * B y z` and
`B x (a * y + b * z) = a * B x y + b * B x z`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (B : type-ℝ-Vector-Space V → type-ℝ-Vector-Space V → ℝ l1)
  where

  is-left-additive-prop-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-left-additive-prop-form-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ y →
            Π-Prop
              ( type-ℝ-Vector-Space V)
              ( λ z →
                Id-Prop
                  ( ℝ-Set l1)
                  ( B (add-ℝ-Vector-Space V x y) z)
                  ( B x z +ℝ B y z))))

  is-left-additive-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-left-additive-form-ℝ-Vector-Space =
    type-Prop is-left-additive-prop-form-ℝ-Vector-Space

  preserves-scalar-mul-left-prop-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  preserves-scalar-mul-left-prop-form-ℝ-Vector-Space =
    Π-Prop
      ( ℝ l1)
      ( λ a →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ x →
            Π-Prop
              ( type-ℝ-Vector-Space V)
              ( λ y →
                Id-Prop
                  ( ℝ-Set l1)
                  ( B (mul-ℝ-Vector-Space V a x) y)
                  ( a *ℝ B x y))))

  preserves-scalar-mul-left-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  preserves-scalar-mul-left-form-ℝ-Vector-Space =
    type-Prop preserves-scalar-mul-left-prop-form-ℝ-Vector-Space

  is-right-additive-prop-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-right-additive-prop-form-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ y →
            Π-Prop
              ( type-ℝ-Vector-Space V)
              ( λ z →
                Id-Prop
                  ( ℝ-Set l1)
                  ( B x (add-ℝ-Vector-Space V y z))
                  ( B x y +ℝ B x z))))

  is-right-additive-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-right-additive-form-ℝ-Vector-Space =
    type-Prop is-right-additive-prop-form-ℝ-Vector-Space

  preserves-scalar-mul-right-prop-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  preserves-scalar-mul-right-prop-form-ℝ-Vector-Space =
    Π-Prop
      ( ℝ l1)
      ( λ a →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ x →
            Π-Prop
              ( type-ℝ-Vector-Space V)
              ( λ y →
                Id-Prop
                  ( ℝ-Set l1)
                  ( B x (mul-ℝ-Vector-Space V a y))
                  ( a *ℝ B x y))))

  preserves-scalar-mul-right-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  preserves-scalar-mul-right-form-ℝ-Vector-Space =
    type-Prop preserves-scalar-mul-right-prop-form-ℝ-Vector-Space

  is-bilinear-prop-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-bilinear-prop-form-ℝ-Vector-Space =
    is-left-additive-prop-form-ℝ-Vector-Space ∧
    preserves-scalar-mul-left-prop-form-ℝ-Vector-Space ∧
    is-right-additive-prop-form-ℝ-Vector-Space ∧
    preserves-scalar-mul-right-prop-form-ℝ-Vector-Space

  is-bilinear-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-bilinear-form-ℝ-Vector-Space =
    type-Prop is-bilinear-prop-form-ℝ-Vector-Space

bilinear-form-ℝ-Vector-Space :
  {l1 l2 : Level} (V : ℝ-Vector-Space l1 l2) → UU (lsuc l1 ⊔ l2)
bilinear-form-ℝ-Vector-Space V =
  type-subtype (is-bilinear-prop-form-ℝ-Vector-Space V)

module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (B : bilinear-form-ℝ-Vector-Space V)
  where

  map-bilinear-form-ℝ-Vector-Space :
    type-ℝ-Vector-Space V → type-ℝ-Vector-Space V → ℝ l1
  map-bilinear-form-ℝ-Vector-Space = pr1 B

  is-left-additive-map-bilinear-form-ℝ-Vector-Space :
    is-left-additive-form-ℝ-Vector-Space V map-bilinear-form-ℝ-Vector-Space
  is-left-additive-map-bilinear-form-ℝ-Vector-Space = pr1 (pr2 B)

  preserves-scalar-mul-left-map-bilinear-form-ℝ-Vector-Space :
    preserves-scalar-mul-left-form-ℝ-Vector-Space
      ( V)
      ( map-bilinear-form-ℝ-Vector-Space)
  preserves-scalar-mul-left-map-bilinear-form-ℝ-Vector-Space = pr1 (pr2 (pr2 B))

  is-right-additive-map-bilinear-form-ℝ-Vector-Space :
    is-right-additive-form-ℝ-Vector-Space
      ( V)
      ( map-bilinear-form-ℝ-Vector-Space)
  is-right-additive-map-bilinear-form-ℝ-Vector-Space = pr1 (pr2 (pr2 (pr2 B)))

  preserves-scalar-mul-right-map-bilinear-form-ℝ-Vector-Space :
    preserves-scalar-mul-right-form-ℝ-Vector-Space
      ( V)
      ( map-bilinear-form-ℝ-Vector-Space)
  preserves-scalar-mul-right-map-bilinear-form-ℝ-Vector-Space =
    pr2 (pr2 (pr2 (pr2 B)))

  abstract
    preserves-scalar-mul-map-bilinear-form-ℝ-Vector-Space :
      (a b : ℝ l1) (u v : type-ℝ-Vector-Space V) →
      map-bilinear-form-ℝ-Vector-Space
        ( mul-ℝ-Vector-Space V a u)
        ( mul-ℝ-Vector-Space V b v) ＝
      (a *ℝ b) *ℝ map-bilinear-form-ℝ-Vector-Space u v
    preserves-scalar-mul-map-bilinear-form-ℝ-Vector-Space a b u v =
      equational-reasoning
        map-bilinear-form-ℝ-Vector-Space
          ( mul-ℝ-Vector-Space V a u)
          ( mul-ℝ-Vector-Space V b v)
        ＝
          a *ℝ map-bilinear-form-ℝ-Vector-Space u (mul-ℝ-Vector-Space V b v)
          by preserves-scalar-mul-left-map-bilinear-form-ℝ-Vector-Space a _ _
        ＝
          a *ℝ (b *ℝ map-bilinear-form-ℝ-Vector-Space u v)
          by
            ap-mul-ℝ
              ( refl)
              ( preserves-scalar-mul-right-map-bilinear-form-ℝ-Vector-Space
                ( b)
                ( _)
                ( _))
        ＝ (a *ℝ b) *ℝ map-bilinear-form-ℝ-Vector-Space u v
          by inv (associative-mul-ℝ _ _ _)
```

## External links

- [Bilinear form](https://en.wikipedia.org/wiki/Bilinear_form) on Wikipedia
