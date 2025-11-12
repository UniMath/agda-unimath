# Real inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.real-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import order-theory.large-posets
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.bilinear-forms-real-vector-spaces
open import foundation.transport-along-identifications
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-vector-spaces

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
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

### The Pythagorean theorem for real inner product spaces

The Pythagorean theorem for real inner product spaces asserts that for
orthogonal `v` and `w`, the norm of `v + w` is the
[square root](real-numbers.square-roots-nonnegative-real-numbers.md) of the sum
of the squared norm of `v` and the squared norm of `w`.

The Pythagorean theorem is the [4th](literature.100-theorems.md#4) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    squared-pythagorean-theorem-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      is-orthogonal-ℝ-Inner-Product-Space V v w →
      squared-norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V v w) ＝
      squared-norm-ℝ-Inner-Product-Space V v +ℝ
      squared-norm-ℝ-Inner-Product-Space V w
    squared-pythagorean-theorem-ℝ-Inner-Product-Space v w v∙w=0 =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
      in
        equational-reasoning
          (v +V w) ∙V (v +V w)
          ＝ (v ∙V v) +ℝ real-ℕ 2 *ℝ (v ∙V w) +ℝ (w ∙V w)
            by squared-norm-add-ℝ-Inner-Product-Space V v w
          ＝ (v ∙V v) +ℝ real-ℕ 2 *ℝ raise-ℝ l1 zero-ℝ +ℝ (w ∙V w)
            by ap-add-ℝ (ap-add-ℝ refl (ap-mul-ℝ refl v∙w=0)) refl
          ＝ (v ∙V v) +ℝ zero-ℝ +ℝ (w ∙V w)
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
          ＝ (v ∙V v) +ℝ (w ∙V w)
            by ap-add-ℝ (right-unit-law-add-ℝ _) refl

    pythagorean-theorem-ℝ-Inner-Product-Space :
      (v w : type-ℝ-Inner-Product-Space V) →
      is-orthogonal-ℝ-Inner-Product-Space V v w →
      norm-ℝ-Inner-Product-Space V (add-ℝ-Inner-Product-Space V v w) ＝
      real-sqrt-ℝ⁰⁺
        ( nonnegative-squared-norm-ℝ-Inner-Product-Space V v +ℝ⁰⁺
          nonnegative-squared-norm-ℝ-Inner-Product-Space V w)
    pythagorean-theorem-ℝ-Inner-Product-Space v w v∙w=0 =
      ap
        ( real-sqrt-ℝ⁰⁺)
        ( eq-ℝ⁰⁺ _ _
          ( squared-pythagorean-theorem-ℝ-Inner-Product-Space v w v∙w=0))
```

### The Cauchy-Schwarz inequality

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Inner-Product-Space l1 l2)
  where

  abstract
    cauchy-schwarz-inequality-ℝ-Inner-Product-Space :
      (u v : type-ℝ-Inner-Product-Space V) →
      leq-ℝ
        ( abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v))
        ( norm-ℝ-Inner-Product-Space V u *ℝ norm-ℝ-Inner-Product-Space V v)
    cauchy-schwarz-inequality-ℝ-Inner-Product-Space u v =
      let
        _∙V_ = inner-product-ℝ-Inner-Product-Space V
        _+V_ = add-ℝ-Inner-Product-Space V
        _-V_ = diff-ℝ-Inner-Product-Space V
        _*V_ = mul-ℝ-Inner-Product-Space V
        norm-V = norm-ℝ-Inner-Product-Space V
        squared-norm-V = squared-norm-ℝ-Inner-Product-Space V
        z =
          ((norm-V u *ℝ squared-norm-V v) *V u) -V
          ((norm-V u *ℝ (u ∙V v)) *V v)
        orthogonal-z-v : is-orthogonal-ℝ-Inner-Product-Space V z v
        orthogonal-z-v =
          equational-reasoning
            z ∙V v
            ＝
              (((norm-V u *ℝ squared-norm-V v) *V u) ∙V v) -ℝ
              (((norm-V u *ℝ (u ∙V v)) *V v) ∙V v)
              by
                right-distributive-inner-product-diff-ℝ-Inner-Product-Space
                  ( V)
                  ( _)
                  ( _)
                  ( _)
            ＝
              (norm-V u *ℝ (v ∙V v)) *ℝ (u ∙V v) -ℝ
              (norm-V u *ℝ (u ∙V v)) *ℝ (v ∙V v)
              by
                ap-diff-ℝ
                  ( is-left-homogeneous-inner-product-ℝ-Inner-Product-Space
                    ( V)
                    ( _)
                    ( _)
                    ( _))
                  ( is-left-homogeneous-inner-product-ℝ-Inner-Product-Space
                    ( V)
                    ( _)
                    ( _)
                    ( _))
            ＝
              (norm-V u *ℝ (v ∙V v)) *ℝ (u ∙V v) -ℝ
              (norm-V u *ℝ (v ∙V v)) *ℝ (u ∙V v)
              by ap-diff-ℝ refl (right-swap-mul-ℝ _ _ _)
            ＝ raise-ℝ l1 zero-ℝ
              by
                eq-sim-ℝ
                  ( transitive-sim-ℝ _ _ _
                    ( sim-raise-ℝ l1 zero-ℝ)
                    ( right-inverse-law-add-ℝ _))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          abs-ℝ (inner-product-ℝ-Inner-Product-Space V u v)
          ≤ real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ (u ∙V v))
            by leq-eq-ℝ (eq-abs-sqrt-square-ℝ _)
          ≤
          ≤ {!   !} by {!   !}
```

## References

{{#bibliography}}
