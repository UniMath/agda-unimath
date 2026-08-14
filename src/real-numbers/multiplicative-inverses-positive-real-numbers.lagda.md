# Multiplicative inverses of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.semigroups

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.cofinal-and-coinitial-strictly-increasing-pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-positive-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-positive-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

If a [real number](real-numbers.dedekind-real-numbers.md) `x` is
[positive](real-numbers.positive-real-numbers.md), then it has a
{{#concept "multiplicative inverse" Disambiguation="positive real numbers" Agda=inv-ℝ⁺}},
a unique, positive real number `y` such that the
[product](real-numbers.multiplication-real-numbers.md) of `x` and `y` is 1.

## Definition

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-left-mul-real-ℝ⁺ :
    cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( l)
      ( l)
  cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-left-mul-real-ℝ⁺ =
    ( ( ( mul-ℝ (real-ℝ⁺ x) ,
          is-pointwise-ε-δ-continuous-map-uniformly-continuous-endomap-ℝ
            ( uniformly-continuous-map-right-mul-ℝ l (real-ℝ⁺ x))) ,
        λ _ _ → preserves-strict-order-left-mul-ℝ⁺ x) ,
      is-cofinal-left-mul-real-ℝ⁺ l x ,
      is-coinitial-left-mul-real-ℝ⁺ l x)

  aut-left-mul-real-ℝ⁺ : Aut (ℝ l)
  aut-left-mul-real-ℝ⁺ =
    aut-cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-ℝ
      ( cofinal-and-coinitial-strictly-increasing-pointwise-ε-δ-continuous-endomap-left-mul-real-ℝ⁺)

  opaque
    real-inv-ℝ⁺ : ℝ l
    real-inv-ℝ⁺ = map-inv-equiv aut-left-mul-real-ℝ⁺ (raise-one-ℝ l)
```

## Properties

### The multiplicative inverse of a positive real number is positive

```agda
module _
  {l : Level} (x⁺@(x , 0<x) : ℝ⁺ l)
  where

  abstract opaque
    unfolding real-inv-ℝ⁺

    is-positive-real-inv-ℝ⁺ : is-positive-ℝ (real-inv-ℝ⁺ x⁺)
    is-positive-real-inv-ℝ⁺ =
      elim-disjunction
        ( is-positive-prop-ℝ (real-inv-ℝ⁺ x⁺))
        ( λ (x<0 , _) → ex-falso (is-not-negative-and-positive-ℝ (x<0 , 0<x)))
        ( pr2)
        ( same-sign-is-positive-mul-ℝ
          ( x)
          ( real-inv-ℝ⁺ x⁺)
          ( inv-tr
            ( is-positive-ℝ)
            ( is-section-map-inv-equiv
              ( aut-left-mul-real-ℝ⁺ x⁺)
              ( raise-one-ℝ l))
            ( is-positive-real-ℝ⁺ (raise-one-ℝ⁺ l))))

  inv-ℝ⁺ : ℝ⁺ l
  inv-ℝ⁺ = (real-inv-ℝ⁺ x⁺ , is-positive-real-inv-ℝ⁺)
```

### Inverse laws of multiplication

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  abstract opaque
    unfolding real-inv-ℝ⁺

    eq-right-inverse-law-mul-ℝ⁺ : x *ℝ⁺ inv-ℝ⁺ x ＝ raise-one-ℝ⁺ l
    eq-right-inverse-law-mul-ℝ⁺ =
      eq-ℝ⁺ _ _
        ( is-section-map-inv-equiv (aut-left-mul-real-ℝ⁺ x) (raise-one-ℝ l))

    eq-left-inverse-law-mul-ℝ⁺ : inv-ℝ⁺ x *ℝ⁺ x ＝ raise-one-ℝ⁺ l
    eq-left-inverse-law-mul-ℝ⁺ =
      commutative-mul-ℝ⁺ _ _ ∙ eq-right-inverse-law-mul-ℝ⁺

    right-inverse-law-mul-ℝ⁺ : sim-ℝ⁺ (x *ℝ⁺ inv-ℝ⁺ x) one-ℝ⁺
    right-inverse-law-mul-ℝ⁺ =
      transitive-sim-ℝ⁺
        ( x *ℝ⁺ inv-ℝ⁺ x)
        ( raise-one-ℝ⁺ l)
        ( one-ℝ⁺)
        ( sim-raise-ℝ' l one-ℝ)
        ( sim-eq-ℝ (ap real-ℝ⁺ eq-right-inverse-law-mul-ℝ⁺))

    left-inverse-law-mul-ℝ⁺ : sim-ℝ⁺ (inv-ℝ⁺ x *ℝ⁺ x) one-ℝ⁺
    left-inverse-law-mul-ℝ⁺ =
      tr
        ( λ y → sim-ℝ⁺ y one-ℝ⁺)
        ( commutative-mul-ℝ⁺ _ _)
        ( right-inverse-law-mul-ℝ⁺)
```

### Multiplication of positive real numbers at a universe level forms a group

```agda
module _
  (l : Level)
  where

  semigroup-mul-ℝ⁺ : Semigroup (lsuc l)
  semigroup-mul-ℝ⁺ =
    ( ℝ⁺-Set l ,
      mul-ℝ⁺ ,
      associative-mul-ℝ⁺)

  group-mul-ℝ⁺ : Group (lsuc l)
  group-mul-ℝ⁺ =
    ( semigroup-mul-ℝ⁺ ,
      ( raise-one-ℝ⁺ l ,
        left-raise-one-law-mul-ℝ⁺ ,
        right-raise-one-law-mul-ℝ⁺) ,
      inv-ℝ⁺ ,
      eq-left-inverse-law-mul-ℝ⁺ ,
      eq-right-inverse-law-mul-ℝ⁺)
```

### The multiplicative inverse operation preserves similarity

```agda
abstract
  preserves-sim-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    sim-ℝ⁺ x y → sim-ℝ⁺ (inv-ℝ⁺ x) (inv-ℝ⁺ y)
  preserves-sim-inv-ℝ⁺ {l1} {l2} x y x~y =
    sim-eq-raise-ℝ
      ( ap
        ( real-ℝ⁺)
        ( is-injective-equiv
          ( equiv-mul-Group (group-mul-ℝ⁺ (l1 ⊔ l2)) (raise-ℝ⁺ l2 x))
          ( equational-reasoning
            raise-ℝ⁺ l2 x *ℝ⁺ raise-ℝ⁺ l2 (inv-ℝ⁺ x)
            ＝ raise-ℝ⁺ l2 (x *ℝ⁺ inv-ℝ⁺ x)
              by eq-ℝ⁺ _ _ (mul-raise-ℝ _ _)
            ＝ raise-ℝ⁺ l2 (raise-one-ℝ⁺ l1)
              by ap (raise-ℝ⁺ l2) (eq-right-inverse-law-mul-ℝ⁺ x)
            ＝ raise-one-ℝ⁺ (l1 ⊔ l2)
              by eq-ℝ⁺ _ _ (raise-raise-ℝ one-ℝ)
            ＝ raise-ℝ⁺ l1 (raise-one-ℝ⁺ l2)
              by eq-ℝ⁺ _ _ (inv (raise-raise-ℝ one-ℝ))
            ＝ raise-ℝ⁺ l1 (y *ℝ⁺ inv-ℝ⁺ y)
              by ap (raise-ℝ⁺ l1) (inv (eq-right-inverse-law-mul-ℝ⁺ y))
            ＝ raise-ℝ⁺ l1 y *ℝ⁺ raise-ℝ⁺ l1 (inv-ℝ⁺ y)
              by eq-ℝ⁺ _ _ (inv (mul-raise-ℝ _ _))
            ＝ raise-ℝ⁺ l2 x *ℝ⁺ raise-ℝ⁺ l1 (inv-ℝ⁺ y)
              by ap-mul-ℝ⁺ (eq-ℝ⁺ _ _ (inv (eq-raise-sim-ℝ x~y))) refl)))
```

### The inclusion of positive rational numbers in the positive real numbers preserves multiplicative inverses

```agda
abstract
  inv-positive-real-ℚ⁺ :
    (q : ℚ⁺) → inv-ℝ⁺ (positive-real-ℚ⁺ q) ＝ positive-real-ℚ⁺ (inv-ℚ⁺ q)
  inv-positive-real-ℚ⁺ q =
    inv
      ( unique-right-inv-Group
        ( group-mul-ℝ⁺ lzero)
        ( positive-real-ℚ⁺ q)
        ( positive-real-ℚ⁺ (inv-ℚ⁺ q))
        ( equational-reasoning
          positive-real-ℚ⁺ q *ℝ⁺ positive-real-ℚ⁺ (inv-ℚ⁺ q)
          ＝ positive-real-ℚ⁺ (q *ℚ⁺ inv-ℚ⁺ q)
            by eq-ℝ⁺ _ _ (mul-real-ℚ _ _)
          ＝ one-ℝ⁺
            by ap positive-real-ℚ⁺ (right-inverse-law-mul-ℚ⁺ q)
          ＝ raise-one-ℝ⁺ lzero
            by eq-raise-ℝ⁺ one-ℝ⁺))

  real-inv-positive-real-ℚ⁺ :
    (q : ℚ⁺) → real-inv-ℝ⁺ (positive-real-ℚ⁺ q) ＝ real-ℚ⁺ (inv-ℚ⁺ q)
  real-inv-positive-real-ℚ⁺ q =
    ap real-ℝ⁺ (inv-positive-real-ℚ⁺ q)
```

### The multiplicative inverse operation reverses inequality

```agda
abstract
  inv-leq-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    leq-ℝ⁺ x y → leq-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-leq-ℝ⁺ x⁺@(x , _) y⁺@(y , _) x≤y =
    leq-not-le-ℝ _ _
      ( λ 1/x<1/y →
        irreflexive-le-ℝ
          ( one-ℝ)
          ( concatenate-le-leq-ℝ
            ( one-ℝ)
            ( x *ℝ real-inv-ℝ⁺ y⁺)
            ( one-ℝ)
            ( preserves-strict-order-left-sim-ℝ _ _ _
              ( right-inverse-law-mul-ℝ⁺ x⁺)
              ( preserves-strict-order-left-mul-ℝ⁺ x⁺ 1/x<1/y))
            ( preserves-order-right-sim-ℝ
              ( right-inverse-law-mul-ℝ⁺ y⁺)
              ( preserves-order-right-mul-ℝ⁺ (inv-ℝ⁺ y⁺) x≤y))))
```

### The multiplicative inverse operation reverses strict inequality

```agda
abstract
  inv-le-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    le-ℝ⁺ x y → le-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-le-ℝ⁺ x⁺@(x , 0<x) y⁺@(y , _) x<y =
    let
      open do-syntax-trunc-Prop (le-prop-ℝ⁺ (inv-ℝ⁺ y⁺) (inv-ℝ⁺ x⁺))
    in do
      (p , x<p , p<y) ← dense-rational-le-ℝ x y x<y
      (q , p<q , q<y) ← dense-rational-le-ℝ _ _ p<y
      let
        p⁺ =
          ( p ,
            is-positive-le-zero-ℚ
              ( reflects-le-real-ℚ (transitive-le-ℝ _ _ _ x<p 0<x)))
        q⁺ = (q , is-positive-le-ℚ⁺ p⁺ (reflects-le-real-ℚ p<q))
      concatenate-leq-le-ℝ
        ( real-inv-ℝ⁺ y⁺)
        ( real-inv-ℝ⁺ (positive-real-ℚ⁺ q⁺))
        ( real-inv-ℝ⁺ x⁺)
        ( inv-leq-ℝ⁺ _ _ (leq-le-ℝ q<y))
        ( concatenate-le-leq-ℝ
          ( real-inv-ℝ⁺ (positive-real-ℚ⁺ q⁺))
          ( real-inv-ℝ⁺ (positive-real-ℚ⁺ p⁺))
          ( real-inv-ℝ⁺ x⁺)
          ( binary-tr
            ( le-ℝ)
            ( ap real-ℝ⁺ (inv (inv-positive-real-ℚ⁺ q⁺)))
            ( ap real-ℝ⁺ (inv (inv-positive-real-ℚ⁺ p⁺)))
            ( preserves-strict-order-real-ℚ (inv-le-ℚ⁺ p⁺ q⁺ (reflects-le-real-ℚ p<q))))
          ( inv-leq-ℝ⁺ _ _ (leq-le-ℝ x<p)))
```

### If `xy = 1`, `y` is the multiplicative inverse of `x`

```agda
abstract
  unique-right-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    sim-ℝ⁺ (x *ℝ⁺ y) one-ℝ⁺ → sim-ℝ⁺ y (inv-ℝ⁺ x)
  unique-right-inv-ℝ⁺ {l1} {l2} x⁺@(x , _) y⁺@(y , _) xy~1 =
    sim-eq-raise-ℝ
      ( ap
        ( real-ℝ⁺)
        ( is-injective-equiv
          ( equiv-mul-Group (group-mul-ℝ⁺ (l1 ⊔ l2)) (raise-ℝ⁺ l2 x⁺))
          ( equational-reasoning
            raise-ℝ⁺ l2 x⁺ *ℝ⁺ raise-ℝ⁺ l1 y⁺
            ＝ raise-ℝ⁺ (l1 ⊔ l2) (x⁺ *ℝ⁺ y⁺)
              by eq-ℝ⁺ _ _ (mul-raise-ℝ x y)
            ＝ raise-ℝ⁺ (l1 ⊔ l2) (raise-one-ℝ⁺ (l1 ⊔ l2))
              by
                ap
                  ( raise-ℝ⁺ (l1 ⊔ l2))
                  ( eq-sim-ℝ⁺ _ _
                    ( transitive-sim-ℝ _ _ _ (sim-raise-ℝ _ _) xy~1))
            ＝ raise-one-ℝ⁺ (l1 ⊔ l2)
              by inv (eq-raise-ℝ⁺ _)
            ＝ raise-ℝ⁺ l2 (raise-one-ℝ⁺ l1)
              by inv (eq-ℝ⁺ _ _ (raise-raise-ℝ {lzero} {l2} {l1} one-ℝ))
            ＝ raise-ℝ⁺ l2 (x⁺ *ℝ⁺ inv-ℝ⁺ x⁺)
              by ap (raise-ℝ⁺ l2) (inv (eq-right-inverse-law-mul-ℝ⁺ x⁺))
            ＝ raise-ℝ⁺ l2 x⁺ *ℝ⁺ raise-ℝ⁺ l2 (inv-ℝ⁺ x⁺)
              by inv (eq-ℝ⁺ _ _ (mul-raise-ℝ _ _)))))
```

### The multiplicative inverse is distributive over multiplication

```agda
abstract
  distributive-inv-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    inv-ℝ⁺ (x *ℝ⁺ y) ＝ inv-ℝ⁺ x *ℝ⁺ inv-ℝ⁺ y
  distributive-inv-mul-ℝ⁺ x⁺@(x , _) y⁺@(y , _) =
    inv
      ( eq-sim-ℝ⁺ _ _
        ( unique-right-inv-ℝ⁺
          ( x⁺ *ℝ⁺ y⁺)
          ( inv-ℝ⁺ x⁺ *ℝ⁺ inv-ℝ⁺ y⁺)
          ( similarity-reasoning-ℝ
            (x *ℝ y) *ℝ (real-inv-ℝ⁺ x⁺ *ℝ real-inv-ℝ⁺ y⁺)
            ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ (y *ℝ real-inv-ℝ⁺ y⁺)
              by sim-eq-ℝ (interchange-law-mul-mul-ℝ _ _ _ _)
            ~ℝ one-ℝ *ℝ one-ℝ
              by
                preserves-sim-mul-ℝ
                  ( right-inverse-law-mul-ℝ⁺ x⁺)
                  ( right-inverse-law-mul-ℝ⁺ y⁺)
            ~ℝ one-ℝ
              by sim-eq-ℝ (right-unit-law-mul-ℝ one-ℝ))))

  distributive-real-inv-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    real-inv-ℝ⁺ (x *ℝ⁺ y) ＝ real-inv-ℝ⁺ x *ℝ real-inv-ℝ⁺ y
  distributive-real-inv-mul-ℝ⁺ x y =
    ap real-ℝ⁺ (distributive-inv-mul-ℝ⁺ x y)
```

### For nonnegative `x`, `(x + ε)⁻¹ x ≤ 1`

```agda
abstract
  leq-one-mul-inv-add-positive-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁺ l2) →
    leq-ℝ (real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x y) *ℝ real-ℝ⁰⁺ x) one-ℝ
  leq-one-mul-inv-add-positive-ℝ⁰⁺ x⁰⁺@(x , _) y⁺@(y , _) =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ x
      ≤ real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ (x +ℝ y)
        by
          preserves-order-left-mul-ℝ⁺
            ( inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
            ( leq-left-add-real-ℝ⁺ x y⁺)
      ≤ one-ℝ
        by
          leq-sim-ℝ
            ( left-inverse-law-mul-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
```

### Cancellation laws

```agda
module _
  {l1 l2 : Level}
  (x⁺@(x , _) : ℝ⁺ l1)
  (y : ℝ l2)
  where

  abstract
    cancel-left-mul-div-ℝ⁺ : sim-ℝ (x *ℝ (real-inv-ℝ⁺ x⁺ *ℝ y)) y
    cancel-left-mul-div-ℝ⁺ =
      similarity-reasoning-ℝ
        x *ℝ (real-inv-ℝ⁺ x⁺ *ℝ y)
        ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ y
          by sim-eq-ℝ (inv (associative-mul-ℝ x _ y))
        ~ℝ one-ℝ *ℝ y
          by preserves-sim-right-mul-ℝ y _ _ (right-inverse-law-mul-ℝ⁺ x⁺)
        ~ℝ y
          by sim-eq-ℝ (left-unit-law-mul-ℝ y)

    cancel-left-div-mul-ℝ⁺ : sim-ℝ (real-inv-ℝ⁺ x⁺ *ℝ (x *ℝ y)) y
    cancel-left-div-mul-ℝ⁺ =
      tr
        ( λ z → sim-ℝ z y)
        ( left-swap-mul-ℝ _ _ _)
        ( cancel-left-mul-div-ℝ⁺)

    cancel-right-mul-div-ℝ⁺ : sim-ℝ ((y *ℝ x) *ℝ real-inv-ℝ⁺ x⁺) y
    cancel-right-mul-div-ℝ⁺ =
      similarity-reasoning-ℝ
        y *ℝ x *ℝ real-inv-ℝ⁺ x⁺
        ~ℝ y *ℝ (x *ℝ real-inv-ℝ⁺ x⁺)
          by sim-eq-ℝ (associative-mul-ℝ y x _)
        ~ℝ y *ℝ one-ℝ
          by preserves-sim-left-mul-ℝ y _ _ (right-inverse-law-mul-ℝ⁺ x⁺)
        ~ℝ y
          by sim-eq-ℝ (right-unit-law-mul-ℝ y)

    cancel-right-div-mul-ℝ⁺ : sim-ℝ ((y *ℝ real-inv-ℝ⁺ x⁺) *ℝ x) y
    cancel-right-div-mul-ℝ⁺ =
      tr
        ( λ z → sim-ℝ z y)
        ( right-swap-mul-ℝ _ _ _)
        ( cancel-right-mul-div-ℝ⁺)
```

### For any positive `c`, we have `c⁻¹ * dist-ℝ (c * x) (c * y) = dist-ℝ x y`

```agda
abstract
  cancel-left-div-mul-dist-ℝ⁺ :
    {l1 l2 l3 : Level} (c : ℝ⁺ l1) (x : ℝ l2) (y : ℝ l3) →
    sim-ℝ
      ( real-inv-ℝ⁺ c *ℝ dist-ℝ (real-ℝ⁺ c *ℝ x) (real-ℝ⁺ c *ℝ y))
      ( dist-ℝ x y)
  cancel-left-div-mul-dist-ℝ⁺ c x y =
    similarity-reasoning-ℝ
      real-inv-ℝ⁺ c *ℝ dist-ℝ (real-ℝ⁺ c *ℝ x) (real-ℝ⁺ c *ℝ y)
      ~ℝ abs-ℝ (real-inv-ℝ⁺ c) *ℝ abs-ℝ (real-ℝ⁺ c *ℝ (x -ℝ y))
        by
          sim-eq-ℝ
            ( ap-mul-ℝ
              ( inv (abs-real-ℝ⁺ (inv-ℝ⁺ c)))
              ( ap abs-ℝ (inv (left-distributive-mul-diff-ℝ _ x y))))
      ~ℝ abs-ℝ (real-inv-ℝ⁺ c *ℝ (real-ℝ⁺ c *ℝ (x -ℝ y)))
        by sim-eq-ℝ (inv (abs-mul-ℝ _ _))
      ~ℝ dist-ℝ x y
        by preserves-sim-abs-ℝ (cancel-left-div-mul-ℝ⁺ c (x -ℝ y))
```
