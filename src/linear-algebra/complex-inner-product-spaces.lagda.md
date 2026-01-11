# Complex inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.complex-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.real-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.complex-vector-spaces
open import linear-algebra.conjugate-symmetric-sesquilinear-forms-complex-vector-spaces
open import linear-algebra.sesquilinear-forms-complex-vector-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

A {{#concept "complex inner product space" Agda=ℂ-Inner-Product-Space}} is a
[complex vector space](linear-algebra.complex-vector-spaces.md) with a
[sesquilinear form](linear-algebra.sesquilinear-forms-complex-vector-spaces.md),
called its
{{#concept "inner product" Disambiguation="on a complex vector space" Agda=inner-product-ℂ-Vector-Space}},
satisfying the following properties:

- [**Conjugate symmetry**](linear-algebra.conjugate-symmetric-sesquilinear-forms-complex-vector-spaces.md):
  for all `u` and `v`, the inner product of `u` and `v` is the
  [conjugate](complex-numbers.conjugation-complex-numbers.md) of the inner
  product of `v` and `u`. Note that this implies the inner product of `v` and
  `v` is a [real complex number](complex-numbers.real-complex-numbers.md).
- **Semidefiniteness**: for all `v`, the inner product of `v` and `v`, as a
  [real number](real-numbers.dedekind-real-numbers.md), is
  [nonnegative](real-numbers.nonnegative-real-numbers.md).
- **Extensionality**: for all `v`, if the inner product of `v` and `v` is zero,
  `v` is the zero vector.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (f : sesquilinear-form-ℂ-Vector-Space V)
  where

  is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space : Prop (l1 ⊔ l2)
  is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        is-nonnegative-prop-ℝ
          ( re-ℂ (map-sesquilinear-form-ℂ-Vector-Space V f x x)))

  is-semidefinite-sesquilinear-form-ℂ-Vector-Space : UU (l1 ⊔ l2)
  is-semidefinite-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space

  is-extensional-prop-sesquilinear-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-extensional-prop-sesquilinear-form-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        ( Id-Prop
          ( ℂ-Set l1)
          ( map-sesquilinear-form-ℂ-Vector-Space V f x x)
          ( raise-ℂ l1 zero-ℂ)) ⇒
        ( Id-Prop
          ( set-ℂ-Vector-Space V)
          ( x)
          ( zero-ℂ-Vector-Space V)))

  is-extensional-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-extensional-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-extensional-prop-sesquilinear-form-ℂ-Vector-Space

  is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space =
    ( is-conjugate-symmetric-prop-sesquilinear-form-ℂ-Vector-Space V f) ∧
    ( is-semidefinite-prop-sesquilinear-form-ℂ-Vector-Space) ∧
    ( is-extensional-prop-sesquilinear-form-ℂ-Vector-Space)

  is-inner-product-sesquilinear-form-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-inner-product-sesquilinear-form-ℂ-Vector-Space =
    type-Prop is-inner-product-prop-sesquilinear-form-ℂ-Vector-Space

inner-product-ℂ-Vector-Space :
  {l1 l2 : Level} → ℂ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
inner-product-ℂ-Vector-Space V =
  Σ ( sesquilinear-form-ℂ-Vector-Space V)
    ( is-inner-product-sesquilinear-form-ℂ-Vector-Space V)

ℂ-Inner-Product-Space : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
ℂ-Inner-Product-Space l1 l2 =
  Σ ( ℂ-Vector-Space l1 l2)
    ( inner-product-ℂ-Vector-Space)

module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  vector-space-ℂ-Inner-Product-Space : ℂ-Vector-Space l1 l2
  vector-space-ℂ-Inner-Product-Space = pr1 V

  sesquilinear-form-inner-product-ℂ-Inner-Product-Space :
    sesquilinear-form-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space
  sesquilinear-form-inner-product-ℂ-Inner-Product-Space = pr1 (pr2 V)

  type-ℂ-Inner-Product-Space : UU l2
  type-ℂ-Inner-Product-Space =
    type-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space

  inner-product-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space → ℂ l1
  inner-product-ℂ-Inner-Product-Space =
    map-sesquilinear-form-ℂ-Vector-Space
      ( vector-space-ℂ-Inner-Product-Space)
      ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

  abstract
    is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space :
      (x y : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space x y ＝
      conjugate-ℂ (inner-product-ℂ-Inner-Product-Space y x)
    is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space =
      pr1 (pr2 (pr2 V))

    is-real-diagonal-inner-product-ℂ-Inner-Product-Space :
      (x : type-ℂ-Inner-Product-Space) →
      is-real-ℂ (inner-product-ℂ-Inner-Product-Space x x)
    is-real-diagonal-inner-product-ℂ-Inner-Product-Space =
      is-real-diagonal-is-conjugate-symmetric-sesquilinear-form-ℂ-Vector-Space
        ( vector-space-ℂ-Inner-Product-Space)
        ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)
        ( is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space)

  squared-norm-ℂ-Inner-Product-Space : type-ℂ-Inner-Product-Space → ℝ l1
  squared-norm-ℂ-Inner-Product-Space v =
    re-ℂ (inner-product-ℂ-Inner-Product-Space v v)

  abstract
    eq-inner-product-squared-norm-ℂ-Inner-Product-Space :
      (v : type-ℂ-Inner-Product-Space) →
      complex-ℝ (squared-norm-ℂ-Inner-Product-Space v) ＝
      inner-product-ℂ-Inner-Product-Space v v
    eq-inner-product-squared-norm-ℂ-Inner-Product-Space v =
      eq-complex-re-is-real-ℂ
        ( _)
        ( is-real-diagonal-inner-product-ℂ-Inner-Product-Space v)

    is-nonnegative-squared-norm-ℂ-Inner-Product-Space :
      (v : type-ℂ-Inner-Product-Space) →
      is-nonnegative-ℝ (squared-norm-ℂ-Inner-Product-Space v)
    is-nonnegative-squared-norm-ℂ-Inner-Product-Space =
      pr1 (pr2 (pr2 (pr2 V)))

  nonnegative-squared-norm-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → ℝ⁰⁺ l1
  nonnegative-squared-norm-ℂ-Inner-Product-Space v =
    ( squared-norm-ℂ-Inner-Product-Space v ,
      is-nonnegative-squared-norm-ℂ-Inner-Product-Space v)

  nonnegative-norm-ℂ-Inner-Product-Space : type-ℂ-Inner-Product-Space → ℝ⁰⁺ l1
  nonnegative-norm-ℂ-Inner-Product-Space v =
    sqrt-ℝ⁰⁺ (nonnegative-squared-norm-ℂ-Inner-Product-Space v)

  norm-ℂ-Inner-Product-Space : type-ℂ-Inner-Product-Space → ℝ l1
  norm-ℂ-Inner-Product-Space v =
    real-ℝ⁰⁺ (nonnegative-norm-ℂ-Inner-Product-Space v)

  ab-ℂ-Inner-Product-Space : Ab l2
  ab-ℂ-Inner-Product-Space =
    ab-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space

  add-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space →
    type-ℂ-Inner-Product-Space
  add-ℂ-Inner-Product-Space = add-Ab ab-ℂ-Inner-Product-Space

  diff-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space →
    type-ℂ-Inner-Product-Space
  diff-ℂ-Inner-Product-Space = right-subtraction-Ab ab-ℂ-Inner-Product-Space

  zero-ℂ-Inner-Product-Space : type-ℂ-Inner-Product-Space
  zero-ℂ-Inner-Product-Space = zero-Ab ab-ℂ-Inner-Product-Space

  mul-ℂ-Inner-Product-Space :
    ℂ l1 → type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space
  mul-ℂ-Inner-Product-Space =
    mul-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space

  mul-real-ℂ-Inner-Product-Space :
    ℝ l1 → type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space
  mul-real-ℂ-Inner-Product-Space x =
    mul-ℂ-Inner-Product-Space (complex-ℝ x)

  neg-ℂ-Inner-Product-Space :
    type-ℂ-Inner-Product-Space → type-ℂ-Inner-Product-Space
  neg-ℂ-Inner-Product-Space = neg-Ab ab-ℂ-Inner-Product-Space

  abstract
    mul-neg-one-ℂ-Inner-Product-Space :
      (v : type-ℂ-Inner-Product-Space) →
      mul-ℂ-Inner-Product-Space (neg-ℂ (raise-ℂ l1 one-ℂ)) v ＝
      neg-ℂ-Inner-Product-Space v
    mul-neg-one-ℂ-Inner-Product-Space =
      mul-neg-one-ℂ-Vector-Space vector-space-ℂ-Inner-Product-Space

    is-left-additive-inner-product-ℂ-Inner-Product-Space :
      (u v w : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space (add-ℂ-Inner-Product-Space u v) w ＝
      ( inner-product-ℂ-Inner-Product-Space u w) +ℂ
      ( inner-product-ℂ-Inner-Product-Space v w)
    is-left-additive-inner-product-ℂ-Inner-Product-Space =
      is-left-additive-sesquilinear-form-ℂ-Vector-Space
        ( vector-space-ℂ-Inner-Product-Space)
        ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

    is-right-additive-inner-product-ℂ-Inner-Product-Space :
      (u v w : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space u (add-ℂ-Inner-Product-Space v w) ＝
      ( inner-product-ℂ-Inner-Product-Space u v) +ℂ
      ( inner-product-ℂ-Inner-Product-Space u w)
    is-right-additive-inner-product-ℂ-Inner-Product-Space =
      is-right-additive-sesquilinear-form-ℂ-Vector-Space
        ( vector-space-ℂ-Inner-Product-Space)
        ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

    preserves-scalar-mul-left-inner-product-ℂ-Inner-Product-Space :
      (a : ℂ l1) (u v : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space (mul-ℂ-Inner-Product-Space a u) v ＝
      a *ℂ inner-product-ℂ-Inner-Product-Space u v
    preserves-scalar-mul-left-inner-product-ℂ-Inner-Product-Space =
      preserves-scalar-mul-left-sesquilinear-form-ℂ-Vector-Space
        ( vector-space-ℂ-Inner-Product-Space)
        ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

    conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space :
      (a : ℂ l1) (u v : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space u (mul-ℂ-Inner-Product-Space a v) ＝
      conjugate-ℂ a *ℂ inner-product-ℂ-Inner-Product-Space u v
    conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space =
      conjugates-scalar-mul-right-sesquilinear-form-ℂ-Vector-Space
        ( vector-space-ℂ-Inner-Product-Space)
        ( sesquilinear-form-inner-product-ℂ-Inner-Product-Space)

    preserves-scalar-mul-real-right-inner-product-ℂ-Inner-Product-Space :
      (a : ℝ l1) (u v : type-ℂ-Inner-Product-Space) →
      inner-product-ℂ-Inner-Product-Space
        ( u)
        ( mul-real-ℂ-Inner-Product-Space a v) ＝
      complex-ℝ a *ℂ inner-product-ℂ-Inner-Product-Space u v
    preserves-scalar-mul-real-right-inner-product-ℂ-Inner-Product-Space a u v =
      ( conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space _ u v) ∙
      ( ap-mul-ℂ (conjugate-complex-ℝ a) refl)
```

## Properties

### `∥av∥² = ∣a∣²∥v∥²`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-mul-ℂ-Inner-Product-Space :
      (a : ℂ l1) (v : type-ℂ-Inner-Product-Space V) →
      squared-norm-ℂ-Inner-Product-Space V (mul-ℂ-Inner-Product-Space V a v) ＝
      squared-magnitude-ℂ a *ℝ squared-norm-ℂ-Inner-Product-Space V v
    squared-norm-mul-ℂ-Inner-Product-Space a v =
      let
        _*V_ = mul-ℂ-Inner-Product-Space V
        _·V_ = inner-product-ℂ-Inner-Product-Space V
      in
        ap
          ( re-ℂ)
          ( equational-reasoning
            ((a *V v) ·V (a *V v))
            ＝ a *ℂ (v ·V (a *V v))
              by
                preserves-scalar-mul-left-inner-product-ℂ-Inner-Product-Space
                  ( V)
                  ( a)
                  ( v)
                  ( a *V v)
            ＝ a *ℂ (conjugate-ℂ a *ℂ (v ·V v))
              by
                ap-mul-ℂ
                  ( refl)
                  ( conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space
                    ( V)
                    ( a)
                    ( v)
                    ( v))
            ＝ (a *ℂ conjugate-ℂ a) *ℂ (v ·V v)
              by inv (associative-mul-ℂ _ _ _)
            ＝
              ( complex-ℝ (squared-magnitude-ℂ a)) *ℂ
              ( complex-ℝ (squared-norm-ℂ-Inner-Product-Space V v))
              by
                ap-mul-ℂ
                  ( eq-squared-magnitude-mul-conjugate-ℂ a)
                  ( inv
                    ( eq-inner-product-squared-norm-ℂ-Inner-Product-Space V v))
            ＝
              complex-ℝ
                ( ( squared-magnitude-ℂ a) *ℝ
                  ( squared-norm-ℂ-Inner-Product-Space V v))
              by mul-complex-ℝ _ _)
```

### `∥av∥ = ∣a∣∥v∥`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    norm-mul-ℂ-Inner-Product-Space :
      (a : ℂ l1) (v : type-ℂ-Inner-Product-Space V) →
      norm-ℂ-Inner-Product-Space V (mul-ℂ-Inner-Product-Space V a v) ＝
      magnitude-ℂ a *ℝ norm-ℂ-Inner-Product-Space V v
    norm-mul-ℂ-Inner-Product-Space a v =
      ( ap
        ( real-sqrt-ℝ⁰⁺)
        ( eq-ℝ⁰⁺
          ( nonnegative-squared-norm-ℂ-Inner-Product-Space
            ( V)
            ( mul-ℂ-Inner-Product-Space V a v))
          ( ( nonnegative-squared-magnitude-ℂ a) *ℝ⁰⁺
            ( nonnegative-squared-norm-ℂ-Inner-Product-Space V v))
          ( squared-norm-mul-ℂ-Inner-Product-Space V a v))) ∙
      ( ap
        ( real-ℝ⁰⁺)
        ( distributive-sqrt-mul-ℝ⁰⁺
          ( nonnegative-squared-magnitude-ℂ a)
          ( nonnegative-squared-norm-ℂ-Inner-Product-Space V v)))

    norm-mul-real-ℂ-Inner-Product-Space :
      (a : ℝ l1) (v : type-ℂ-Inner-Product-Space V) →
      norm-ℂ-Inner-Product-Space V (mul-real-ℂ-Inner-Product-Space V a v) ＝
      abs-ℝ a *ℝ norm-ℂ-Inner-Product-Space V v
    norm-mul-real-ℂ-Inner-Product-Space a v =
      ( norm-mul-ℂ-Inner-Product-Space (complex-ℝ a) v) ∙
      ( ap-mul-ℝ (magnitude-complex-ℝ a) refl)
```

### Negative laws for the inner product

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    right-negative-law-inner-product-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      inner-product-ℂ-Inner-Product-Space V u (neg-ℂ-Inner-Product-Space V v) ＝
      neg-ℂ (inner-product-ℂ-Inner-Product-Space V u v)
    right-negative-law-inner-product-ℂ-Inner-Product-Space u v =
      equational-reasoning
        inner-product-ℂ-Inner-Product-Space V u (neg-ℂ-Inner-Product-Space V v)
        ＝
          inner-product-ℂ-Inner-Product-Space
            ( V)
            ( u)
            ( mul-ℂ-Inner-Product-Space V (neg-ℂ (raise-ℂ l1 one-ℂ)) v)
          by
            ap
              ( inner-product-ℂ-Inner-Product-Space V u)
              ( inv (mul-neg-one-ℂ-Inner-Product-Space V v))
        ＝
          ( conjugate-ℂ (neg-ℂ (raise-ℂ l1 one-ℂ))) *ℂ
          ( inner-product-ℂ-Inner-Product-Space V u v)
          by
            conjugates-scalar-mul-right-inner-product-ℂ-Inner-Product-Space
              ( V)
              ( neg-ℂ (raise-ℂ l1 one-ℂ))
              ( u)
              ( v)
        ＝
          ( neg-ℂ (raise-ℂ l1 (conjugate-ℂ one-ℂ))) *ℂ
          ( inner-product-ℂ-Inner-Product-Space V u v)
          by ap-mul-ℂ (ap neg-ℂ (conjugate-raise-ℂ l1 _)) refl
        ＝
          ( neg-ℂ (raise-ℂ l1 one-ℂ)) *ℂ
          ( inner-product-ℂ-Inner-Product-Space V u v)
          by ap-mul-ℂ (ap neg-ℂ (ap (raise-ℂ l1) conjugate-one-ℂ)) refl
        ＝ neg-ℂ (raise-ℂ l1 one-ℂ *ℂ inner-product-ℂ-Inner-Product-Space V u v)
          by left-negative-law-mul-ℂ _ _
        ＝ neg-ℂ (inner-product-ℂ-Inner-Product-Space V u v)
          by ap neg-ℂ (left-raise-one-law-mul-ℂ _)

    left-negative-law-inner-product-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      inner-product-ℂ-Inner-Product-Space V (neg-ℂ-Inner-Product-Space V u) v ＝
      neg-ℂ (inner-product-ℂ-Inner-Product-Space V u v)
    left-negative-law-inner-product-ℂ-Inner-Product-Space u v =
      equational-reasoning
        inner-product-ℂ-Inner-Product-Space V (neg-ℂ-Inner-Product-Space V u) v
        ＝
          conjugate-ℂ
            ( inner-product-ℂ-Inner-Product-Space
              ( V)
              ( v)
              ( neg-ℂ-Inner-Product-Space V u))
          by is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space V _ _
        ＝ conjugate-ℂ (neg-ℂ (inner-product-ℂ-Inner-Product-Space V v u))
          by
            ap
              ( conjugate-ℂ)
              ( right-negative-law-inner-product-ℂ-Inner-Product-Space v u)
        ＝
          conjugate-ℂ
            ( neg-ℂ (conjugate-ℂ (inner-product-ℂ-Inner-Product-Space V u v)))
          by
            ap
              ( conjugate-ℂ ∘ neg-ℂ)
              ( is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space
                ( V)
                ( v)
                ( u))
        ＝ neg-ℂ (inner-product-ℂ-Inner-Product-Space V u v)
          by ap neg-ℂ (is-involution-conjugate-ℂ _)

    negative-law-inner-product-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      inner-product-ℂ-Inner-Product-Space V
        ( neg-ℂ-Inner-Product-Space V u)
        ( neg-ℂ-Inner-Product-Space V v) ＝
      inner-product-ℂ-Inner-Product-Space V u v
    negative-law-inner-product-ℂ-Inner-Product-Space u v =
      ( left-negative-law-inner-product-ℂ-Inner-Product-Space _ _) ∙
      ( ap neg-ℂ (right-negative-law-inner-product-ℂ-Inner-Product-Space _ _)) ∙
      ( neg-neg-ℂ _)
```

### `∥-v∥² = ∥v∥²`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-neg-ℂ-Inner-Product-Space :
      (v : type-ℂ-Inner-Product-Space V) →
      squared-norm-ℂ-Inner-Product-Space V (neg-ℂ-Inner-Product-Space V v) ＝
      squared-norm-ℂ-Inner-Product-Space V v
    squared-norm-neg-ℂ-Inner-Product-Space v =
      ap re-ℂ (negative-law-inner-product-ℂ-Inner-Product-Space V v v)
```

### `∥u+v∥² = ∥u∥² + 2Re⟨u,v⟩ + ∥v∥²`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-add-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      squared-norm-ℂ-Inner-Product-Space V (add-ℂ-Inner-Product-Space V u v) ＝
      ( squared-norm-ℂ-Inner-Product-Space V u) +ℝ
      ( real-ℕ 2 *ℝ re-ℂ (inner-product-ℂ-Inner-Product-Space V u v)) +ℝ
      ( squared-norm-ℂ-Inner-Product-Space V v)
    squared-norm-add-ℂ-Inner-Product-Space u v =
      let
        _+V_ = add-ℂ-Inner-Product-Space V
        _·V_ = inner-product-ℂ-Inner-Product-Space V
      in
        ( ap
          ( re-ℂ)
          ( equational-reasoning
            (u +V v) ·V (u +V v)
            ＝ (u ·V (u +V v)) +ℂ (v ·V (u +V v))
              by is-left-additive-inner-product-ℂ-Inner-Product-Space V _ _ _
            ＝ ((u ·V u) +ℂ (u ·V v)) +ℂ ((v ·V u) +ℂ (v ·V v))
              by
                ap-add-ℂ
                  ( is-right-additive-inner-product-ℂ-Inner-Product-Space
                    ( V)
                    ( u)
                    ( u)
                    ( v))
                  ( is-right-additive-inner-product-ℂ-Inner-Product-Space
                    ( V)
                    ( v)
                    ( u)
                    ( v))
            ＝ ((u ·V u) +ℂ (u ·V v)) +ℂ (conjugate-ℂ (u ·V v) +ℂ (v ·V v))
              by
                ap-add-ℂ
                  ( refl)
                  ( ap-add-ℂ
                    ( is-conjugate-symmetric-inner-product-ℂ-Inner-Product-Space
                      ( V)
                      ( v)
                      ( u))
                    ( refl))
            ＝ ((u ·V u) +ℂ (u ·V v) +ℂ conjugate-ℂ (u ·V v)) +ℂ (v ·V v)
              by inv (associative-add-ℂ _ _ _)
            ＝ ((u ·V u) +ℂ ((u ·V v) +ℂ conjugate-ℂ (u ·V v))) +ℂ (v ·V v)
              by ap-add-ℂ (associative-add-ℂ _ _ _) refl
            ＝
              (u ·V u) +ℂ complex-ℝ (re-ℂ (u ·V v) +ℝ re-ℂ (u ·V v)) +ℂ (v ·V v)
              by ap-add-ℂ (ap-add-ℂ refl (right-add-conjugate-ℂ _)) refl)) ∙
        ( ap-add-ℝ (ap-add-ℝ refl (inv (left-mul-real-ℕ 2 _))) refl)
```

### `∥u-v∥² = ∥u∥² - 2Re⟨u,v⟩ + ∥v∥²`

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-diff-ℂ-Inner-Product-Space :
      (u v : type-ℂ-Inner-Product-Space V) →
      squared-norm-ℂ-Inner-Product-Space V (diff-ℂ-Inner-Product-Space V u v) ＝
      ( squared-norm-ℂ-Inner-Product-Space V u) -ℝ
      ( real-ℕ 2 *ℝ re-ℂ (inner-product-ℂ-Inner-Product-Space V u v)) +ℝ
      ( squared-norm-ℂ-Inner-Product-Space V v)
    squared-norm-diff-ℂ-Inner-Product-Space u v =
      let
        _+V_ = add-ℂ-Inner-Product-Space V
        _-V_ = diff-ℂ-Inner-Product-Space V
        _·V_ = inner-product-ℂ-Inner-Product-Space V
        neg-V = neg-ℂ-Inner-Product-Space V
      in
        equational-reasoning
        squared-norm-ℂ-Inner-Product-Space V (u -V v)
        ＝
          ( squared-norm-ℂ-Inner-Product-Space V u) +ℝ
          ( real-ℕ 2 *ℝ re-ℂ (u ·V neg-V v)) +ℝ
          ( squared-norm-ℂ-Inner-Product-Space V (neg-V v))
          by squared-norm-add-ℂ-Inner-Product-Space V u (neg-V v)
        ＝
          ( squared-norm-ℂ-Inner-Product-Space V u) +ℝ
          ( real-ℕ 2 *ℝ neg-ℝ (re-ℂ (u ·V v))) +ℝ
          ( squared-norm-ℂ-Inner-Product-Space V v)
          by
            ap-add-ℝ
              ( ap-add-ℝ
                ( refl {x = squared-norm-ℂ-Inner-Product-Space V u})
                ( ap-mul-ℝ
                  ( refl)
                  ( ap
                    ( re-ℂ)
                    ( right-negative-law-inner-product-ℂ-Inner-Product-Space
                      ( V)
                      ( u)
                      ( v)))))
              ( squared-norm-neg-ℂ-Inner-Product-Space V v)
        ＝
          ( squared-norm-ℂ-Inner-Product-Space V u) +ℝ
          ( neg-ℝ ( real-ℕ 2 *ℝ re-ℂ (u ·V v))) +ℝ
          ( squared-norm-ℂ-Inner-Product-Space V v)
          by ap-add-ℝ (ap-add-ℝ refl (right-negative-law-mul-ℝ _ _)) refl
```
