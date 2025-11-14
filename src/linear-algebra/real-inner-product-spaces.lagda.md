# Real inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-} -- DO NOT SUBMIT

module linear-algebra.real-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.bilinear-forms-real-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.extensionality-squares-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

An
{{#concept "inner product" WDID=Q23924662 WD="inner product" Disambiguation="on a real vector space" Agda=inner-product-ℝ-Vector-Space}}
on a [real vector space](linear-algebra.real-vector-spaces.md) `V` is a
commutative [bilinear form](linear-algebra.bilinear-forms-real-vector-spaces.md)
`i : V → V → ℝ` such that for all `v : V`, `i v v` is
[nonnegative](real-numbers.nonnegative-real-numbers.md), and if `i v v = 0`,
then `v` is the zero vector.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (B : bilinear-form-ℝ-Vector-Space V)
  where

  is-semidefinite-prop-bilinear-form-ℝ-Vector-Space : Prop (l1 ⊔ l2)
  is-semidefinite-prop-bilinear-form-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ v → is-nonnegative-prop-ℝ (map-bilinear-form-ℝ-Vector-Space V B v v))

  is-extensional-prop-bilinear-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-extensional-prop-bilinear-form-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ v →
        hom-Prop
          ( Id-Prop
            ( ℝ-Set l1)
            ( map-bilinear-form-ℝ-Vector-Space V B v v)
            ( raise-ℝ l1 zero-ℝ))
          ( is-zero-prop-ℝ-Vector-Space V v))

  is-inner-product-prop-bilinear-form-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-inner-product-prop-bilinear-form-ℝ-Vector-Space =
    is-commutative-prop-bilinear-form-ℝ-Vector-Space V B ∧
    is-semidefinite-prop-bilinear-form-ℝ-Vector-Space ∧
    is-extensional-prop-bilinear-form-ℝ-Vector-Space

  is-inner-product-bilinear-form-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-inner-product-bilinear-form-ℝ-Vector-Space =
    type-Prop is-inner-product-prop-bilinear-form-ℝ-Vector-Space

inner-product-ℝ-Vector-Space :
  {l1 l2 : Level} → ℝ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
inner-product-ℝ-Vector-Space V =
  type-subtype (is-inner-product-prop-bilinear-form-ℝ-Vector-Space V)

ℝ-Inner-Product-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Inner-Product-Space l1 l2 =
  Σ (ℝ-Vector-Space l1 l2) inner-product-ℝ-Vector-Space

module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  vector-space-ℝ-Inner-Product-Space : ℝ-Vector-Space l1 l2
  vector-space-ℝ-Inner-Product-Space = pr1 V

  bilinear-form-inner-product-ℝ-Inner-Product-Space :
    bilinear-form-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space
  bilinear-form-inner-product-ℝ-Inner-Product-Space = pr1 (pr2 V)

  type-ℝ-Inner-Product-Space : UU l2
  type-ℝ-Inner-Product-Space =
    type-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  inner-product-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space → ℝ l1
  inner-product-ℝ-Inner-Product-Space =
    map-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space)

  zero-ℝ-Inner-Product-Space : type-ℝ-Inner-Product-Space
  zero-ℝ-Inner-Product-Space =
    zero-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  is-zero-prop-ℝ-Inner-Product-Space : subtype l2 type-ℝ-Inner-Product-Space
  is-zero-prop-ℝ-Inner-Product-Space =
    is-zero-prop-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  is-zero-ℝ-Inner-Product-Space : type-ℝ-Inner-Product-Space → UU l2
  is-zero-ℝ-Inner-Product-Space =
    is-zero-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  add-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space →
    type-ℝ-Inner-Product-Space
  add-ℝ-Inner-Product-Space =
    add-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  neg-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space
  neg-ℝ-Inner-Product-Space =
    neg-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  diff-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space →
    type-ℝ-Inner-Product-Space
  diff-ℝ-Inner-Product-Space =
    diff-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  mul-ℝ-Inner-Product-Space :
    ℝ l1 → type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space
  mul-ℝ-Inner-Product-Space =
    mul-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space

  is-left-additive-inner-product-ℝ-Inner-Product-Space :
    is-left-additive-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( inner-product-ℝ-Inner-Product-Space)
  is-left-additive-inner-product-ℝ-Inner-Product-Space =
    is-left-additive-map-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space)

  is-left-homogeneous-inner-product-ℝ-Inner-Product-Space :
    is-left-homogeneous-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( inner-product-ℝ-Inner-Product-Space)
  is-left-homogeneous-inner-product-ℝ-Inner-Product-Space =
    is-left-homogeneous-map-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space)

  is-right-additive-inner-product-ℝ-Inner-Product-Space :
    is-right-additive-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( inner-product-ℝ-Inner-Product-Space)
  is-right-additive-inner-product-ℝ-Inner-Product-Space =
    is-right-additive-map-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space)

  is-right-homogeneous-inner-product-ℝ-Inner-Product-Space :
    is-right-homogeneous-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( inner-product-ℝ-Inner-Product-Space)
  is-right-homogeneous-inner-product-ℝ-Inner-Product-Space =
    is-right-homogeneous-map-bilinear-form-ℝ-Vector-Space
      ( vector-space-ℝ-Inner-Product-Space)
      ( bilinear-form-inner-product-ℝ-Inner-Product-Space)

  is-nonnegative-diagonal-inner-product-ℝ-Inner-Product-Space :
    (v : type-ℝ-Inner-Product-Space) →
    is-nonnegative-ℝ (inner-product-ℝ-Inner-Product-Space v v)
  is-nonnegative-diagonal-inner-product-ℝ-Inner-Product-Space =
    pr1 (pr2 (pr2 (pr2 V)))

  is-orthogonal-prop-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space → Prop (lsuc l1)
  is-orthogonal-prop-ℝ-Inner-Product-Space v w =
    Id-Prop
      ( ℝ-Set l1)
      ( inner-product-ℝ-Inner-Product-Space v w)
      ( raise-ℝ l1 zero-ℝ)

  is-orthogonal-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → type-ℝ-Inner-Product-Space → UU (lsuc l1)
  is-orthogonal-ℝ-Inner-Product-Space v w =
    type-Prop (is-orthogonal-prop-ℝ-Inner-Product-Space v w)

  commutative-inner-product-ℝ-Inner-Product-Space :
    (v w : type-ℝ-Inner-Product-Space) →
    inner-product-ℝ-Inner-Product-Space v w ＝
    inner-product-ℝ-Inner-Product-Space w v
  commutative-inner-product-ℝ-Inner-Product-Space = pr1 (pr2 (pr2 V))

  symmetric-is-orthogonal-ℝ-Inner-Product-Space :
    (v w : type-ℝ-Inner-Product-Space) →
    is-orthogonal-ℝ-Inner-Product-Space v w →
    is-orthogonal-ℝ-Inner-Product-Space w v
  symmetric-is-orthogonal-ℝ-Inner-Product-Space v w =
    tr
      ( _＝ raise-ℝ l1 zero-ℝ)
      ( commutative-inner-product-ℝ-Inner-Product-Space v w)

  is-extensional-diagonal-inner-product-ℝ-Inner-Product-Space :
    (v : type-ℝ-Inner-Product-Space) →
    is-orthogonal-ℝ-Inner-Product-Space v v →
    v ＝ zero-ℝ-Inner-Product-Space
  is-extensional-diagonal-inner-product-ℝ-Inner-Product-Space =
    pr2 (pr2 (pr2 (pr2 V)))

  nonnegative-squared-norm-ℝ-Inner-Product-Space :
    type-ℝ-Inner-Product-Space → ℝ⁰⁺ l1
  nonnegative-squared-norm-ℝ-Inner-Product-Space v =
    ( inner-product-ℝ-Inner-Product-Space v v ,
      is-nonnegative-diagonal-inner-product-ℝ-Inner-Product-Space v)

  squared-norm-ℝ-Inner-Product-Space : type-ℝ-Inner-Product-Space → ℝ l1
  squared-norm-ℝ-Inner-Product-Space v =
    real-ℝ⁰⁺ (nonnegative-squared-norm-ℝ-Inner-Product-Space v)

  nonnegative-norm-ℝ-Inner-Product-Space : type-ℝ-Inner-Product-Space → ℝ⁰⁺ l1
  nonnegative-norm-ℝ-Inner-Product-Space v =
    sqrt-ℝ⁰⁺ (nonnegative-squared-norm-ℝ-Inner-Product-Space v)

  norm-ℝ-Inner-Product-Space : type-ℝ-Inner-Product-Space → ℝ l1
  norm-ℝ-Inner-Product-Space v =
    real-ℝ⁰⁺ (nonnegative-norm-ℝ-Inner-Product-Space v)

  mul-neg-one-ℝ-Inner-Product-Space :
    (v : type-ℝ-Inner-Product-Space) →
    mul-ℝ-Inner-Product-Space (neg-ℝ (raise-ℝ l1 one-ℝ)) v ＝
    neg-ℝ-Inner-Product-Space v
  mul-neg-one-ℝ-Inner-Product-Space =
    mul-neg-one-ℝ-Vector-Space vector-space-ℝ-Inner-Product-Space
```

## Properties

### Negative laws of the inner product

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    right-negative-law-inner-product-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      inner-product-ℝ-Inner-Product-Space V v (neg-ℝ-Inner-Product-Space V w) ＝
      neg-ℝ (inner-product-ℝ-Inner-Product-Space V v w)
    right-negative-law-inner-product-ℝ-Inner-Product-Space v w =
      equational-reasoning
        inner-product-ℝ-Inner-Product-Space V v (neg-ℝ-Inner-Product-Space V w)
        ＝
          inner-product-ℝ-Inner-Product-Space
            ( V)
            ( v)
            ( mul-ℝ-Inner-Product-Space
              ( V)
              ( neg-ℝ (raise-ℝ l1 one-ℝ))
              ( w))
          by
            ap
              ( inner-product-ℝ-Inner-Product-Space V v)
              ( inv (mul-neg-one-ℝ-Inner-Product-Space V w))
        ＝
          neg-ℝ (raise-ℝ l1 one-ℝ) *ℝ
          inner-product-ℝ-Inner-Product-Space V v w
          by is-right-homogeneous-inner-product-ℝ-Inner-Product-Space V _ _ _
        ＝
          neg-ℝ (raise-ℝ l1 one-ℝ *ℝ inner-product-ℝ-Inner-Product-Space V v w)
          by left-negative-law-mul-ℝ _ _
        ＝
          neg-ℝ (one-ℝ *ℝ inner-product-ℝ-Inner-Product-Space V v w)
          by
            ap
              ( neg-ℝ)
              ( eq-sim-ℝ
                ( preserves-sim-right-mul-ℝ _ _ _ (sim-raise-ℝ' l1 one-ℝ)))
        ＝ neg-ℝ (inner-product-ℝ-Inner-Product-Space V v w)
          by ap neg-ℝ (left-unit-law-mul-ℝ _)

    left-negative-law-inner-product-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      inner-product-ℝ-Inner-Product-Space V (neg-ℝ-Inner-Product-Space V v) w ＝
      neg-ℝ (inner-product-ℝ-Inner-Product-Space V v w)
    left-negative-law-inner-product-ℝ-Inner-Product-Space v w =
      equational-reasoning
        inner-product-ℝ-Inner-Product-Space V (neg-ℝ-Inner-Product-Space V v) w
        ＝
          inner-product-ℝ-Inner-Product-Space
            ( V)
            ( w)
            ( neg-ℝ-Inner-Product-Space V v)
          by commutative-inner-product-ℝ-Inner-Product-Space V _ _
        ＝ neg-ℝ (inner-product-ℝ-Inner-Product-Space V w v)
          by right-negative-law-inner-product-ℝ-Inner-Product-Space w v
        ＝ neg-ℝ (inner-product-ℝ-Inner-Product-Space V v w)
          by ap neg-ℝ (commutative-inner-product-ℝ-Inner-Product-Space V w v)
```

### The inner product is distributive over subtraction

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    right-distributive-inner-product-diff-ℝ-Inner-Product-Space :
      (u v w : type-ℝ-Inner-Product-Space V) →
      inner-product-ℝ-Inner-Product-Space V
        ( diff-ℝ-Inner-Product-Space V u v)
        ( w) ＝
      ( inner-product-ℝ-Inner-Product-Space V u w -ℝ
        inner-product-ℝ-Inner-Product-Space V v w)
    right-distributive-inner-product-diff-ℝ-Inner-Product-Space u v w =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
        _-V_ = diff-ℝ-Inner-Product-Space V
        neg-V = neg-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          (u -V v) ∙V w
          ＝ (u ∙V w) +ℝ (neg-V v ∙V w)
            by is-left-additive-inner-product-ℝ-Inner-Product-Space V _ _ _
          ＝ (u ∙V w) -ℝ (v ∙V w)
            by
              ap-add-ℝ
                ( refl)
                ( left-negative-law-inner-product-ℝ-Inner-Product-Space V _ _)
```

### Orthogonality is preserved by scalar multiplication

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    preserves-is-orthogonal-left-mul-ℝ-Inner-Product-Space :
      (c : ℝ l1) (v w : type-ℝ-Inner-Product-Space V) →
      is-orthogonal-ℝ-Inner-Product-Space V v w →
      is-orthogonal-ℝ-Inner-Product-Space V (mul-ℝ-Inner-Product-Space V c v) w
    preserves-is-orthogonal-left-mul-ℝ-Inner-Product-Space c v w v∙w=0 =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
        _*V_ = mul-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          (c *V v) ∙V w
          ＝ c *ℝ (v ∙V w)
            by is-left-homogeneous-inner-product-ℝ-Inner-Product-Space V _ _ _
          ＝ c *ℝ raise-ℝ l1 zero-ℝ
            by ap-mul-ℝ refl v∙w=0
          ＝ c *ℝ zero-ℝ
            by
              eq-sim-ℝ (preserves-sim-left-mul-ℝ _ _ _ (sim-raise-ℝ' l1 zero-ℝ))
          ＝ raise-ℝ l1 zero-ℝ
            by
              eq-sim-ℝ
                ( transitive-sim-ℝ _ _ _
                  ( sim-raise-ℝ l1 zero-ℝ)
                  ( right-zero-law-mul-ℝ c))
```

### The norm of the sum of two vectors

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-add-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      squared-norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V v w) ＝
      ( squared-norm-ℝ-Inner-Product-Space V v +ℝ
        real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V v w +ℝ
        squared-norm-ℝ-Inner-Product-Space V w)
    squared-norm-add-ℝ-Inner-Product-Space v w =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          (v +V w) ∙V (v +V w)
          ＝ (v ∙V (v +V w)) +ℝ (w ∙V (v +V w))
            by is-left-additive-inner-product-ℝ-Inner-Product-Space V _ _ _
          ＝ ((v ∙V v) +ℝ (v ∙V w)) +ℝ ((w ∙V v) +ℝ (w ∙V w))
            by
              ap-add-ℝ
                ( is-right-additive-inner-product-ℝ-Inner-Product-Space V _ _ _)
                ( is-right-additive-inner-product-ℝ-Inner-Product-Space V _ _ _)
          ＝ (v ∙V v) +ℝ (v ∙V w) +ℝ (w ∙V v) +ℝ (w ∙V w)
            by inv (associative-add-ℝ _ _ _)
          ＝ (v ∙V v) +ℝ ((v ∙V w) +ℝ (w ∙V v)) +ℝ (w ∙V w)
            by ap-add-ℝ (associative-add-ℝ _ _ _) refl
          ＝ (v ∙V v) +ℝ ((v ∙V w) +ℝ (v ∙V w)) +ℝ (w ∙V w)
            by
              ap-add-ℝ
                ( ap-add-ℝ
                  ( refl)
                  ( ap-add-ℝ
                    ( refl)
                    ( commutative-inner-product-ℝ-Inner-Product-Space V w v)))
                ( refl)
          ＝ (v ∙V v) +ℝ real-ℕ 2 *ℝ (v ∙V w) +ℝ (w ∙V w)
            by ap-add-ℝ (ap-add-ℝ refl (inv (left-mul-real-ℕ 2 _))) refl
```

### The norm is absolutely homogeneous

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-mul-ℝ-Inner-Product-Space :
      (c : ℝ l1) (v : type-ℝ-Inner-Product-Space V) →
      squared-norm-ℝ-Inner-Product-Space V (mul-ℝ-Inner-Product-Space V c v) ＝
      square-ℝ c *ℝ squared-norm-ℝ-Inner-Product-Space V v
    squared-norm-mul-ℝ-Inner-Product-Space c v =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
        _*V_ = mul-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          (c *V v) ∙V (c *V v)
          ＝ c *ℝ (v ∙V (c *V v))
            by is-left-homogeneous-inner-product-ℝ-Inner-Product-Space V _ _ _
          ＝ c *ℝ (c *ℝ (v ∙V v))
            by
              ap-mul-ℝ
                ( refl)
                ( is-right-homogeneous-inner-product-ℝ-Inner-Product-Space
                  ( V)
                  ( _)
                  ( _)
                  ( _))
          ＝ (c *ℝ c) *ℝ (v ∙V v)
            by inv (associative-mul-ℝ _ _ _)

    is-absolutely-homogeneous-norm-ℝ-Inner-Product-Space :
      (c : ℝ l1) (v : type-ℝ-Inner-Product-Space V) →
      norm-ℝ-Inner-Product-Space V (mul-ℝ-Inner-Product-Space V c v) ＝
      abs-ℝ c *ℝ norm-ℝ-Inner-Product-Space V v
    is-absolutely-homogeneous-norm-ℝ-Inner-Product-Space c v =
      let
        _*V_ = mul-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          real-sqrt-ℝ⁰⁺
            ( nonnegative-squared-norm-ℝ-Inner-Product-Space V (c *V v))
          ＝
            real-sqrt-ℝ⁰⁺
              ( nonnegative-square-ℝ c *ℝ⁰⁺
                nonnegative-squared-norm-ℝ-Inner-Product-Space V v)
            by
              ap
                ( real-sqrt-ℝ⁰⁺)
                ( eq-ℝ⁰⁺ _ _ (squared-norm-mul-ℝ-Inner-Product-Space c v))
          ＝
            real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ c) *ℝ
            norm-ℝ-Inner-Product-Space V v
            by ap real-ℝ⁰⁺ (distributive-sqrt-mul-ℝ⁰⁺ _ _)
          ＝ abs-ℝ c *ℝ norm-ℝ-Inner-Product-Space V v
            by ap-mul-ℝ (inv (eq-abs-sqrt-square-ℝ c)) refl
```

### The norm of `-v` is the norm of `v`

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-neg-ℝ-Inner-Product-Space :
      (v : type-ℝ-Inner-Product-Space V) →
      squared-norm-ℝ-Inner-Product-Space V (neg-ℝ-Inner-Product-Space V v) ＝
      squared-norm-ℝ-Inner-Product-Space V v
    squared-norm-neg-ℝ-Inner-Product-Space v =
      equational-reasoning
        squared-norm-ℝ-Inner-Product-Space V (neg-ℝ-Inner-Product-Space V v)
        ＝
          squared-norm-ℝ-Inner-Product-Space V
            ( mul-ℝ-Inner-Product-Space
              ( V)
              ( neg-ℝ (raise-ℝ l1 one-ℝ))
              ( v))
          by
            ap
              ( squared-norm-ℝ-Inner-Product-Space V)
              ( inv (mul-neg-one-ℝ-Inner-Product-Space V v))
        ＝
          square-ℝ (neg-ℝ (raise-ℝ l1 one-ℝ)) *ℝ
          squared-norm-ℝ-Inner-Product-Space V v
          by squared-norm-mul-ℝ-Inner-Product-Space V _ _
        ＝
          square-ℝ (raise-ℝ l1 one-ℝ) *ℝ
          squared-norm-ℝ-Inner-Product-Space V v
          by ap-mul-ℝ (square-neg-ℝ _) refl
        ＝
          raise-ℝ l1 (square-ℝ one-ℝ) *ℝ
          squared-norm-ℝ-Inner-Product-Space V v
          by ap-mul-ℝ (square-raise-ℝ l1 one-ℝ) refl
        ＝ raise-ℝ l1 one-ℝ *ℝ squared-norm-ℝ-Inner-Product-Space V v
          by ap-mul-ℝ (ap (raise-ℝ l1) (left-unit-law-mul-ℝ one-ℝ)) refl
        ＝ raise-ℝ l1 (one-ℝ *ℝ squared-norm-ℝ-Inner-Product-Space V v)
          by mul-left-raise-ℝ _ _ _
        ＝ one-ℝ *ℝ squared-norm-ℝ-Inner-Product-Space V v
          by inv (eq-raise-ℝ _)
        ＝ squared-norm-ℝ-Inner-Product-Space V v
          by left-unit-law-mul-ℝ _
```

### The norm of the difference of two vectors

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-norm-diff-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      squared-norm-ℝ-Inner-Product-Space V (diff-ℝ-Inner-Product-Space V v w) ＝
      ( squared-norm-ℝ-Inner-Product-Space V v -ℝ
        real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V v w +ℝ
        squared-norm-ℝ-Inner-Product-Space V w)
    squared-norm-diff-ℝ-Inner-Product-Space v w =
      equational-reasoning
        squared-norm-ℝ-Inner-Product-Space V (diff-ℝ-Inner-Product-Space V v w)
        ＝
          squared-norm-ℝ-Inner-Product-Space V v +ℝ
          ( real-ℕ 2 *ℝ
            inner-product-ℝ-Inner-Product-Space V
              ( v)
              ( neg-ℝ-Inner-Product-Space V w))
          +ℝ
          squared-norm-ℝ-Inner-Product-Space V (neg-ℝ-Inner-Product-Space V w)
          by squared-norm-add-ℝ-Inner-Product-Space V _ _
        ＝
          squared-norm-ℝ-Inner-Product-Space V v +ℝ
          ( real-ℕ 2 *ℝ
            neg-ℝ (inner-product-ℝ-Inner-Product-Space V v w)) +ℝ
          squared-norm-ℝ-Inner-Product-Space V w
          by
            ap-add-ℝ
              ( ap-add-ℝ
                ( refl)
                ( ap-mul-ℝ
                  ( refl)
                  ( right-negative-law-inner-product-ℝ-Inner-Product-Space
                    ( V)
                    ( v)
                    ( w))))
              ( squared-norm-neg-ℝ-Inner-Product-Space V w)
        ＝
          squared-norm-ℝ-Inner-Product-Space V v -ℝ
          real-ℕ 2 *ℝ inner-product-ℝ-Inner-Product-Space V v w +ℝ
          squared-norm-ℝ-Inner-Product-Space V w
          by
            ap-add-ℝ
              ( ap-add-ℝ
                ( refl)
                ( right-negative-law-mul-ℝ _ _))
              ( refl)
```

### The real inner product space of the real numbers

```agda
bilinear-form-mul-ℝ :
  (l : Level) → bilinear-form-ℝ-Vector-Space (real-vector-space-ℝ l)
bilinear-form-mul-ℝ l =
  ( mul-ℝ ,
    right-distributive-mul-add-ℝ ,
    associative-mul-ℝ ,
    left-distributive-mul-add-ℝ ,
    λ c x y → left-swap-mul-ℝ x c y)

is-inner-product-bilinear-form-mul-ℝ :
  (l : Level) →
  is-inner-product-bilinear-form-ℝ-Vector-Space
    ( real-vector-space-ℝ l)
    ( bilinear-form-mul-ℝ l)
is-inner-product-bilinear-form-mul-ℝ l =
  ( commutative-mul-ℝ ,
    is-nonnegative-square-ℝ ,
    eq-zero-eq-zero-square-ℝ)

real-inner-product-space-ℝ : (l : Level) → ℝ-Inner-Product-Space l (lsuc l)
real-inner-product-space-ℝ l =
  ( real-vector-space-ℝ l ,
    bilinear-form-mul-ℝ l ,
    is-inner-product-bilinear-form-mul-ℝ l)
```

## External links

- [Inner product space](https://en.wikipedia.org/wiki/Inner_product_space) on
  Wikipedia
- [inner product space](https://ncatlab.org/nlab/show/inner+product+space) on
  $n$Lab

## References

{{#bibliography}}
