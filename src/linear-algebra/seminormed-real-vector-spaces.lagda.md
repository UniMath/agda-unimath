# Seminormed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.seminormed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.real-vector-spaces

open import metric-spaces.pseudometric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A
{{#concept "seminorm" WDID=Q1416088 WD="seminorm" Disambiguation="on a real vector space" Agda=seminorm-ℝ-Vector-Space}}
on a [real vector space](linear-algebra.real-vector-spaces.md) `V` is a
[real](real-numbers.dedekind-real-numbers.md)-valued function `p` on the vector
space such that `p(x + y) ≤ p(x) + p(y)` for all `x` and `y` in `V`, and
`p(c * x) = |c| * p(x)` for all real numbers `c` and `x` in `V`.

These conditions imply that `p(0) = 0` and that `p` is nonnegative.

A real vector space equipped with such a seminorm is called a
{{#concept "seminormed space" WD="seminormed space" WDID=Q63793693 Agda=Seminormed-ℝ-Vector-Space}}.
A seminormed space has an induced
[pseudometric structure](metric-spaces.pseudometric-spaces.md) defined by the
neighborhood relation that `v` and `w` are in an `ε`-neighborhood of each other
if `p(v - w) ≤ ε`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Vector-Space l1 l2)
  (p : type-ℝ-Vector-Space V → ℝ l1)
  where

  is-triangular-prop-seminorm-ℝ-Vector-Space : Prop (l1 ⊔ l2)
  is-triangular-prop-seminorm-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ y → leq-prop-ℝ (p (add-ℝ-Vector-Space V x y)) (p x +ℝ p y)))

  is-triangular-seminorm-ℝ-Vector-Space : UU (l1 ⊔ l2)
  is-triangular-seminorm-ℝ-Vector-Space =
    type-Prop is-triangular-prop-seminorm-ℝ-Vector-Space

  is-absolutely-homogeneous-prop-seminorm-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-absolutely-homogeneous-prop-seminorm-ℝ-Vector-Space =
    Π-Prop
      ( ℝ l1)
      ( λ c →
        Π-Prop
          ( type-ℝ-Vector-Space V)
          ( λ x →
            Id-Prop
              ( ℝ-Set l1)
              ( p (mul-ℝ-Vector-Space V c x))
              ( abs-ℝ c *ℝ p x)))

  is-absolutely-homogeneous-seminorm-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-absolutely-homogeneous-seminorm-ℝ-Vector-Space =
    type-Prop is-absolutely-homogeneous-prop-seminorm-ℝ-Vector-Space

  is-seminorm-prop-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-seminorm-prop-ℝ-Vector-Space =
    is-triangular-prop-seminorm-ℝ-Vector-Space ∧
    is-absolutely-homogeneous-prop-seminorm-ℝ-Vector-Space

  is-seminorm-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-seminorm-ℝ-Vector-Space = type-Prop is-seminorm-prop-ℝ-Vector-Space

seminorm-ℝ-Vector-Space :
  {l1 l2 : Level} → ℝ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
seminorm-ℝ-Vector-Space V =
  type-subtype (is-seminorm-prop-ℝ-Vector-Space V)

Seminormed-ℝ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Seminormed-ℝ-Vector-Space l1 l2 =
  Σ (ℝ-Vector-Space l1 l2) seminorm-ℝ-Vector-Space
```

## Properties

### Vector space properties

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  vector-space-Seminormed-ℝ-Vector-Space : ℝ-Vector-Space l1 l2
  vector-space-Seminormed-ℝ-Vector-Space = pr1 V

  set-Seminormed-ℝ-Vector-Space : Set l2
  set-Seminormed-ℝ-Vector-Space =
    set-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  type-Seminormed-ℝ-Vector-Space : UU l2
  type-Seminormed-ℝ-Vector-Space =
    type-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  seminorm-Seminormed-ℝ-Vector-Space :
    seminorm-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space
  seminorm-Seminormed-ℝ-Vector-Space = pr2 V

  map-seminorm-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space → ℝ l1
  map-seminorm-Seminormed-ℝ-Vector-Space =
    pr1 seminorm-Seminormed-ℝ-Vector-Space

  zero-Seminormed-ℝ-Vector-Space : type-Seminormed-ℝ-Vector-Space
  zero-Seminormed-ℝ-Vector-Space =
    zero-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  is-zero-prop-Seminormed-ℝ-Vector-Space :
    subtype l2 type-Seminormed-ℝ-Vector-Space
  is-zero-prop-Seminormed-ℝ-Vector-Space =
    is-zero-prop-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  is-zero-Seminormed-ℝ-Vector-Space : type-Seminormed-ℝ-Vector-Space → UU l2
  is-zero-Seminormed-ℝ-Vector-Space =
    is-zero-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  add-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space → type-Seminormed-ℝ-Vector-Space →
    type-Seminormed-ℝ-Vector-Space
  add-Seminormed-ℝ-Vector-Space =
    add-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  mul-Seminormed-ℝ-Vector-Space :
    ℝ l1 → type-Seminormed-ℝ-Vector-Space → type-Seminormed-ℝ-Vector-Space
  mul-Seminormed-ℝ-Vector-Space =
    mul-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  neg-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space → type-Seminormed-ℝ-Vector-Space
  neg-Seminormed-ℝ-Vector-Space =
    neg-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  diff-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space → type-Seminormed-ℝ-Vector-Space →
    type-Seminormed-ℝ-Vector-Space
  diff-Seminormed-ℝ-Vector-Space v w =
    add-Seminormed-ℝ-Vector-Space v (neg-Seminormed-ℝ-Vector-Space w)

  right-inverse-law-add-Seminormed-ℝ-Vector-Space :
    (v : type-Seminormed-ℝ-Vector-Space) →
    add-Seminormed-ℝ-Vector-Space v (neg-Seminormed-ℝ-Vector-Space v) ＝
    zero-Seminormed-ℝ-Vector-Space
  right-inverse-law-add-Seminormed-ℝ-Vector-Space =
    right-inverse-law-add-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  add-diff-Seminormed-ℝ-Vector-Space :
    (v w x : type-Seminormed-ℝ-Vector-Space) →
    add-Seminormed-ℝ-Vector-Space
      ( diff-Seminormed-ℝ-Vector-Space v w)
      ( diff-Seminormed-ℝ-Vector-Space w x) ＝
    diff-Seminormed-ℝ-Vector-Space v x
  add-diff-Seminormed-ℝ-Vector-Space =
    add-diff-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  neg-neg-Seminormed-ℝ-Vector-Space :
    (v : type-Seminormed-ℝ-Vector-Space) →
    neg-Seminormed-ℝ-Vector-Space (neg-Seminormed-ℝ-Vector-Space v) ＝ v
  neg-neg-Seminormed-ℝ-Vector-Space =
    neg-neg-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  left-zero-law-mul-Seminormed-ℝ-Vector-Space :
    (v : type-Seminormed-ℝ-Vector-Space) →
    mul-Seminormed-ℝ-Vector-Space (raise-ℝ l1 zero-ℝ) v ＝
    zero-Seminormed-ℝ-Vector-Space
  left-zero-law-mul-Seminormed-ℝ-Vector-Space =
    left-zero-law-mul-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  mul-neg-one-Seminormed-ℝ-Vector-Space :
    (v : type-Seminormed-ℝ-Vector-Space) →
    mul-Seminormed-ℝ-Vector-Space (neg-ℝ (raise-ℝ l1 one-ℝ)) v ＝
    neg-Seminormed-ℝ-Vector-Space v
  mul-neg-one-Seminormed-ℝ-Vector-Space =
    mul-neg-one-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space

  distributive-neg-diff-Seminormed-ℝ-Vector-Space :
    (v w : type-Seminormed-ℝ-Vector-Space) →
    neg-Seminormed-ℝ-Vector-Space (diff-Seminormed-ℝ-Vector-Space v w) ＝
    diff-Seminormed-ℝ-Vector-Space w v
  distributive-neg-diff-Seminormed-ℝ-Vector-Space =
    neg-right-subtraction-Ab
      ( ab-ℝ-Vector-Space vector-space-Seminormed-ℝ-Vector-Space)

  triangular-Seminormed-ℝ-Vector-Space :
    (v w : type-Seminormed-ℝ-Vector-Space) →
    leq-ℝ
      ( map-seminorm-Seminormed-ℝ-Vector-Space
        ( add-Seminormed-ℝ-Vector-Space v w))
      ( map-seminorm-Seminormed-ℝ-Vector-Space v +ℝ
        map-seminorm-Seminormed-ℝ-Vector-Space w)
  triangular-Seminormed-ℝ-Vector-Space =
    pr1 (pr2 seminorm-Seminormed-ℝ-Vector-Space)

  is-absolutely-homogeneous-Seminormed-ℝ-Vector-Space :
    (c : ℝ l1) (v : type-Seminormed-ℝ-Vector-Space) →
    map-seminorm-Seminormed-ℝ-Vector-Space
      ( mul-Seminormed-ℝ-Vector-Space c v) ＝
    abs-ℝ c *ℝ map-seminorm-Seminormed-ℝ-Vector-Space v
  is-absolutely-homogeneous-Seminormed-ℝ-Vector-Space =
    pr2 (pr2 seminorm-Seminormed-ℝ-Vector-Space)

  dist-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space → type-Seminormed-ℝ-Vector-Space → ℝ l1
  dist-Seminormed-ℝ-Vector-Space v w =
    map-seminorm-Seminormed-ℝ-Vector-Space
      ( diff-Seminormed-ℝ-Vector-Space v w)
```

### The seminorm of the zero vector is zero

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  abstract
    is-zero-seminorm-zero-Seminormed-ℝ-Vector-Space :
      map-seminorm-Seminormed-ℝ-Vector-Space
        ( V)
        ( zero-Seminormed-ℝ-Vector-Space V) ＝
      raise-ℝ l1 zero-ℝ
    is-zero-seminorm-zero-Seminormed-ℝ-Vector-Space =
      equational-reasoning
        map-seminorm-Seminormed-ℝ-Vector-Space
          ( V)
          ( zero-Seminormed-ℝ-Vector-Space V)
        ＝
          map-seminorm-Seminormed-ℝ-Vector-Space
              ( V)
              ( mul-Seminormed-ℝ-Vector-Space
                ( V)
                ( raise-ℝ l1 zero-ℝ)
                ( zero-Seminormed-ℝ-Vector-Space V))
          by
            ap
              ( map-seminorm-Seminormed-ℝ-Vector-Space V)
              ( inv (left-zero-law-mul-Seminormed-ℝ-Vector-Space V _))
        ＝
          ( abs-ℝ (raise-ℝ l1 zero-ℝ)) *ℝ
          ( map-seminorm-Seminormed-ℝ-Vector-Space
            ( V)
            ( zero-Seminormed-ℝ-Vector-Space V))
          by is-absolutely-homogeneous-Seminormed-ℝ-Vector-Space V _ _
        ＝
          ( raise-ℝ l1 (abs-ℝ zero-ℝ)) *ℝ
          ( map-seminorm-Seminormed-ℝ-Vector-Space
            ( V)
            ( zero-Seminormed-ℝ-Vector-Space V))
          by ap-mul-ℝ (abs-raise-ℝ l1 _) refl
        ＝
          ( raise-zero-ℝ l1) *ℝ
          ( map-seminorm-Seminormed-ℝ-Vector-Space
            ( V)
            ( zero-Seminormed-ℝ-Vector-Space V))
          by ap-mul-ℝ (ap (raise-ℝ l1) abs-zero-ℝ) refl
        ＝ raise-zero-ℝ l1
          by left-raise-zero-law-mul-ℝ _

    is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space :
      (v : type-Seminormed-ℝ-Vector-Space V) →
      dist-Seminormed-ℝ-Vector-Space V v v ＝ raise-ℝ l1 zero-ℝ
    is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space v =
      ( ap
        ( map-seminorm-Seminormed-ℝ-Vector-Space V)
        ( right-inverse-law-add-Seminormed-ℝ-Vector-Space V v)) ∙
      ( is-zero-seminorm-zero-Seminormed-ℝ-Vector-Space)

    sim-zero-diagonal-dist-Semiormed-ℝ-Vector-Space :
      (v : type-Seminormed-ℝ-Vector-Space V) →
      sim-ℝ (dist-Seminormed-ℝ-Vector-Space V v v) zero-ℝ
    sim-zero-diagonal-dist-Semiormed-ℝ-Vector-Space v =
      inv-tr
        ( λ x → sim-ℝ x zero-ℝ)
        ( is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space v)
        ( sim-raise-ℝ' l1 zero-ℝ)
```

### The seminorm of the negation of a vector is equal to the seminorm of the vector

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  abstract
    seminorm-neg-Seminormed-ℝ-Vector-Space :
      (v : type-Seminormed-ℝ-Vector-Space V) →
      map-seminorm-Seminormed-ℝ-Vector-Space
        ( V)
        ( neg-Seminormed-ℝ-Vector-Space V v) ＝
      map-seminorm-Seminormed-ℝ-Vector-Space V v
    seminorm-neg-Seminormed-ℝ-Vector-Space v =
      equational-reasoning
        map-seminorm-Seminormed-ℝ-Vector-Space
          ( V)
          ( neg-Seminormed-ℝ-Vector-Space V v)
        ＝
          map-seminorm-Seminormed-ℝ-Vector-Space
            ( V)
            ( mul-Seminormed-ℝ-Vector-Space
              ( V)
              ( neg-ℝ (raise-ℝ l1 one-ℝ))
              ( v))
          by
            ap
              ( map-seminorm-Seminormed-ℝ-Vector-Space V)
              ( inv (mul-neg-one-Seminormed-ℝ-Vector-Space V v))
        ＝
          ( abs-ℝ (neg-ℝ (raise-ℝ l1 one-ℝ))) *ℝ
          ( map-seminorm-Seminormed-ℝ-Vector-Space V v)
          by is-absolutely-homogeneous-Seminormed-ℝ-Vector-Space V _ _
        ＝
          ( abs-ℝ (raise-ℝ l1 one-ℝ)) *ℝ
          ( map-seminorm-Seminormed-ℝ-Vector-Space V v)
          by ap-mul-ℝ (abs-neg-ℝ _) refl
        ＝ abs-ℝ one-ℝ *ℝ map-seminorm-Seminormed-ℝ-Vector-Space V v
          by
            eq-sim-ℝ
              ( preserves-sim-right-mul-ℝ _ _ _
                ( preserves-sim-abs-ℝ (sim-raise-ℝ' l1 one-ℝ)))
        ＝ one-ℝ *ℝ map-seminorm-Seminormed-ℝ-Vector-Space V v
          by ap-mul-ℝ (abs-real-ℝ⁺ one-ℝ⁺) refl
        ＝ map-seminorm-Seminormed-ℝ-Vector-Space V v
          by left-unit-law-mul-ℝ _

    commutative-dist-Seminormed-ℝ-Vector-Space :
      (v w : type-Seminormed-ℝ-Vector-Space V) →
      dist-Seminormed-ℝ-Vector-Space V v w ＝
      dist-Seminormed-ℝ-Vector-Space V w v
    commutative-dist-Seminormed-ℝ-Vector-Space v w =
      ( inv
        ( ap
          ( map-seminorm-Seminormed-ℝ-Vector-Space V)
          ( distributive-neg-diff-Seminormed-ℝ-Vector-Space V w v))) ∙
      ( seminorm-neg-Seminormed-ℝ-Vector-Space _)
```

### The distance function on a seminormed vector space satisfies the triangle inequality

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  abstract
    triangular-dist-Seminormed-ℝ-Vector-Space :
      (v w x : type-Seminormed-ℝ-Vector-Space V) →
      leq-ℝ
        ( dist-Seminormed-ℝ-Vector-Space V v x)
        ( dist-Seminormed-ℝ-Vector-Space V v w +ℝ
          dist-Seminormed-ℝ-Vector-Space V w x)
    triangular-dist-Seminormed-ℝ-Vector-Space v w x =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          dist-Seminormed-ℝ-Vector-Space V v x
          ≤ map-seminorm-Seminormed-ℝ-Vector-Space
            ( V)
            ( add-Seminormed-ℝ-Vector-Space
              ( V)
              ( diff-Seminormed-ℝ-Vector-Space V v w)
              ( diff-Seminormed-ℝ-Vector-Space V w x))
            by
              leq-eq-ℝ
                ( ap
                  ( map-seminorm-Seminormed-ℝ-Vector-Space V)
                  ( inv (add-diff-Seminormed-ℝ-Vector-Space V v w x)))
          ≤ ( dist-Seminormed-ℝ-Vector-Space V v w) +ℝ
            ( dist-Seminormed-ℝ-Vector-Space V w x)
            by triangular-Seminormed-ℝ-Vector-Space V _ _
```

### The seminorm of a vector is nonnegative

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  abstract
    is-nonnegative-seminorm-Seminormed-ℝ-Vector-Space :
      (v : type-Seminormed-ℝ-Vector-Space V) →
      is-nonnegative-ℝ (map-seminorm-Seminormed-ℝ-Vector-Space V v)
    is-nonnegative-seminorm-Seminormed-ℝ-Vector-Space v =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        reflects-leq-left-mul-ℝ⁺
          ( positive-real-ℕ⁺ (2 , λ ()))
          ( zero-ℝ)
          ( map-seminorm-Seminormed-ℝ-Vector-Space V v)
          ( chain-of-inequalities
              real-ℕ 2 *ℝ zero-ℝ
              ≤ zero-ℝ
                by leq-sim-ℝ (right-zero-law-mul-ℝ _)
              ≤ raise-ℝ l1 zero-ℝ
                by leq-sim-ℝ (sim-raise-ℝ l1 zero-ℝ)
              ≤ dist-Seminormed-ℝ-Vector-Space V v v
                by
                  leq-eq-ℝ
                    ( inv (is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space V v))
              ≤ ( map-seminorm-Seminormed-ℝ-Vector-Space V v) +ℝ
                ( map-seminorm-Seminormed-ℝ-Vector-Space
                  ( V)
                  ( neg-Seminormed-ℝ-Vector-Space V v))
                by triangular-Seminormed-ℝ-Vector-Space V _ _
              ≤ ( map-seminorm-Seminormed-ℝ-Vector-Space V v) +ℝ
                ( map-seminorm-Seminormed-ℝ-Vector-Space V v)
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( refl)
                      ( seminorm-neg-Seminormed-ℝ-Vector-Space V v))
              ≤ real-ℕ 2 *ℝ map-seminorm-Seminormed-ℝ-Vector-Space V v
                by leq-eq-ℝ (inv (left-mul-real-ℕ 2 _)))

  nonnegative-seminorm-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-seminorm-Seminormed-ℝ-Vector-Space v =
    ( map-seminorm-Seminormed-ℝ-Vector-Space V v ,
      is-nonnegative-seminorm-Seminormed-ℝ-Vector-Space v)
```

### The pseudometric space induced by a seminorm

```agda
module _
  {l1 l2 : Level} (V : Seminormed-ℝ-Vector-Space l1 l2)
  where

  nonnegative-dist-Seminormed-ℝ-Vector-Space :
    type-Seminormed-ℝ-Vector-Space V → type-Seminormed-ℝ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-dist-Seminormed-ℝ-Vector-Space v w =
    ( dist-Seminormed-ℝ-Vector-Space V v w ,
      is-nonnegative-seminorm-Seminormed-ℝ-Vector-Space V _)

  neighborhood-prop-Seminormed-ℝ-Vector-Space :
    ℚ⁺ → Relation-Prop l1 (type-Seminormed-ℝ-Vector-Space V)
  neighborhood-prop-Seminormed-ℝ-Vector-Space ε v w =
    leq-prop-ℝ
      ( dist-Seminormed-ℝ-Vector-Space V v w)
      ( real-ℚ⁺ ε)

  neighborhood-Seminormed-ℝ-Vector-Space :
    ℚ⁺ → Relation l1 (type-Seminormed-ℝ-Vector-Space V)
  neighborhood-Seminormed-ℝ-Vector-Space d =
    type-Relation-Prop (neighborhood-prop-Seminormed-ℝ-Vector-Space d)

  abstract
    refl-neighborhood-Seminormed-ℝ-Vector-Space :
      (ε : ℚ⁺) (v : type-Seminormed-ℝ-Vector-Space V) →
      neighborhood-Seminormed-ℝ-Vector-Space ε v v
    refl-neighborhood-Seminormed-ℝ-Vector-Space ε v =
      leq-le-ℝ
        ( preserves-le-left-sim-ℝ
          ( real-ℚ⁺ ε)
          ( zero-ℝ)
          ( dist-Seminormed-ℝ-Vector-Space V v v)
          ( symmetric-sim-ℝ
            ( sim-zero-diagonal-dist-Semiormed-ℝ-Vector-Space V v))
          ( preserves-is-positive-real-ℚ (is-positive-rational-ℚ⁺ ε)))

    symmetric-neighborhood-Seminormed-ℝ-Vector-Space :
      (d : ℚ⁺) (v w : type-Seminormed-ℝ-Vector-Space V) →
      neighborhood-Seminormed-ℝ-Vector-Space d v w →
      neighborhood-Seminormed-ℝ-Vector-Space d w v
    symmetric-neighborhood-Seminormed-ℝ-Vector-Space d v w =
      tr
        ( λ z → leq-ℝ z (real-ℚ⁺ d))
        ( commutative-dist-Seminormed-ℝ-Vector-Space V v w)

    triangular-neighborhood-Seminormed-ℝ-Vector-Space :
      (v w x : type-Seminormed-ℝ-Vector-Space V) (d1 d2 : ℚ⁺) →
      neighborhood-Seminormed-ℝ-Vector-Space d2 w x →
      neighborhood-Seminormed-ℝ-Vector-Space d1 v w →
      neighborhood-Seminormed-ℝ-Vector-Space (d1 +ℚ⁺ d2) v x
    triangular-neighborhood-Seminormed-ℝ-Vector-Space
      v w x d1 d2 Nd2wx Nd1vw =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
        dist-Seminormed-ℝ-Vector-Space V v x
        ≤ ( dist-Seminormed-ℝ-Vector-Space V v w) +ℝ
          ( dist-Seminormed-ℝ-Vector-Space V w x)
          by triangular-dist-Seminormed-ℝ-Vector-Space V v w x
        ≤ real-ℚ⁺ d1 +ℝ real-ℚ⁺ d2
          by preserves-leq-add-ℝ Nd1vw Nd2wx
        ≤ real-ℚ⁺ (d1 +ℚ⁺ d2)
          by leq-eq-ℝ (add-real-ℚ _ _)

    saturated-neighborhood-Seminormed-ℝ-Vector-Space :
      (d : ℚ⁺) (v w : type-Seminormed-ℝ-Vector-Space V) →
      ((δ : ℚ⁺) → neighborhood-Seminormed-ℝ-Vector-Space (d +ℚ⁺ δ) v w) →
      neighborhood-Seminormed-ℝ-Vector-Space d v w
    saturated-neighborhood-Seminormed-ℝ-Vector-Space d v w H =
      saturated-leq-ℝ⁰⁺
        ( nonnegative-dist-Seminormed-ℝ-Vector-Space v w)
        ( nonnegative-real-ℚ⁺ d)
        ( λ δ →
          inv-tr
            ( leq-ℝ (dist-Seminormed-ℝ-Vector-Space V v w))
            ( add-real-ℚ _ _)
            ( H δ))

  pseudometric-structure-Seminormed-ℝ-Vector-Space :
    Pseudometric-Structure l1 (type-Seminormed-ℝ-Vector-Space V)
  pseudometric-structure-Seminormed-ℝ-Vector-Space =
    ( neighborhood-prop-Seminormed-ℝ-Vector-Space ,
      refl-neighborhood-Seminormed-ℝ-Vector-Space ,
      symmetric-neighborhood-Seminormed-ℝ-Vector-Space ,
      triangular-neighborhood-Seminormed-ℝ-Vector-Space ,
      saturated-neighborhood-Seminormed-ℝ-Vector-Space)

  pseudometric-space-Seminormed-ℝ-Vector-Space : Pseudometric-Space l2 l1
  pseudometric-space-Seminormed-ℝ-Vector-Space =
    ( type-Seminormed-ℝ-Vector-Space V ,
      pseudometric-structure-Seminormed-ℝ-Vector-Space)
```

### The real numbers are a seminormed vector space over themselves with seminorm `x ↦ |x|`

```agda
seminormed-real-vector-space-ℝ :
  (l : Level) → Seminormed-ℝ-Vector-Space l (lsuc l)
seminormed-real-vector-space-ℝ l =
  ( real-vector-space-ℝ l , abs-ℝ , triangle-inequality-abs-ℝ , abs-mul-ℝ)
```
