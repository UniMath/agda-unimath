# The standard metric space of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-space-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.monotonic-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

[Inequality](elementary-number-theory.inequality-rational-numbers.md) on the
[rational numbers](elementary-number-theory.rational-numbers.md) induces a
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `ℚ` where `x y : ℚ` are in a `d`-neighborhood when `y ≤ x + d` and
`x ≤ y + d`, i.e., if the
[distance](elementary-number-theory.distance-rational-numbers.md) between `x`
and `y` is less than or equal to `d`. This is a
[metric structure](metric-spaces.metric-spaces.md) on `ℚ` that defines the
{{#concept "standard metric space of rational numbers" Agda=metric-space-ℚ}}.

## Definitions

### The standard neighborhood relation on the rational numbers

```agda
lower-neighborhood-prop-ℚ : (d : ℚ⁺) (x y : ℚ) → Prop lzero
lower-neighborhood-prop-ℚ d x y =
  leq-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d))

lower-neighborhood-ℚ : (d : ℚ⁺) (x y : ℚ) → UU lzero
lower-neighborhood-ℚ d x y = type-Prop (lower-neighborhood-prop-ℚ d x y)

is-prop-lower-neighborhood-ℚ :
  (d : ℚ⁺) (x y : ℚ) → is-prop (lower-neighborhood-ℚ d x y)
is-prop-lower-neighborhood-ℚ d x y =
  is-prop-type-Prop (lower-neighborhood-prop-ℚ d x y)

neighborhood-prop-ℚ : Rational-Neighborhood-Relation lzero ℚ
neighborhood-prop-ℚ d x y =
  product-Prop
    ( lower-neighborhood-prop-ℚ d x y)
    ( lower-neighborhood-prop-ℚ d y x)

neighborhood-ℚ : (d : ℚ⁺) (x y : ℚ) → UU lzero
neighborhood-ℚ d x y = type-Prop (neighborhood-prop-ℚ d x y)
```

## Properties

### The standard neighborhood relation on the rational numbers is a metric

```agda
is-reflexive-neighborhood-ℚ :
  is-reflexive-Rational-Neighborhood-Relation neighborhood-prop-ℚ
is-reflexive-neighborhood-ℚ d x =
  diagonal-product
    ( leq-ℚ x (x +ℚ (rational-ℚ⁺ d)))
    ( leq-le-ℚ {x} {x +ℚ (rational-ℚ⁺ d)} (le-right-add-rational-ℚ⁺ x d))

is-symmetric-neighborhood-ℚ :
  is-symmetric-Rational-Neighborhood-Relation neighborhood-prop-ℚ
is-symmetric-neighborhood-ℚ d x y (H , K) = (K , H)

abstract
  is-triangular-neighborhood-ℚ :
    is-triangular-Rational-Neighborhood-Relation neighborhood-prop-ℚ
  pr1 (is-triangular-neighborhood-ℚ x y z d₁ d₂ Hyz Hxy) =
    tr
      ( leq-ℚ z)
      ( associative-add-ℚ x (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
      ( transitive-leq-ℚ
        ( z)
        ( y +ℚ (rational-ℚ⁺ d₂))
        ( x +ℚ (rational-ℚ⁺ d₁) +ℚ (rational-ℚ⁺ d₂))
        ( preserves-leq-left-add-ℚ
          ( rational-ℚ⁺ d₂)
          ( y)
          ( x +ℚ (rational-ℚ⁺ d₁))
          ( pr1 Hxy))
        ( pr1 Hyz))
  pr2 (is-triangular-neighborhood-ℚ x y z d₁ d₂ Hyz Hxy) =
    tr
      ( leq-ℚ x)
      ( ap (z +ℚ_) (commutative-add-ℚ (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁)))
      ( tr
        ( leq-ℚ x)
        ( associative-add-ℚ z (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁))
        ( transitive-leq-ℚ
          ( x)
          ( y +ℚ (rational-ℚ⁺ d₁))
          ( z +ℚ (rational-ℚ⁺ d₂) +ℚ (rational-ℚ⁺ d₁))
          ( ( preserves-leq-left-add-ℚ
            ( rational-ℚ⁺ d₁)
            ( y)
            ( z +ℚ (rational-ℚ⁺ d₂))
            ( pr2 Hyz)))
          ( pr2 Hxy)))

  is-saturated-neighborhood-ℚ :
    is-saturated-Rational-Neighborhood-Relation neighborhood-prop-ℚ
  is-saturated-neighborhood-ℚ ε x y H =
    map-inv-equiv
      ( equiv-leq-leq-add-positive-ℚ y (x +ℚ rational-ℚ⁺ ε))
      ( λ δ →
        inv-tr
          ( leq-ℚ y)
          ( associative-add-ℚ x (rational-ℚ⁺ ε) (rational-ℚ⁺ δ))
          ( pr1 (H δ))) ,
    map-inv-equiv
      ( equiv-leq-leq-add-positive-ℚ x (y +ℚ rational-ℚ⁺ ε))
      ( λ δ →
        inv-tr
          ( leq-ℚ x)
          ( associative-add-ℚ y (rational-ℚ⁺ ε) (rational-ℚ⁺ δ))
          ( pr2 (H δ)))

pseudometric-space-ℚ : Pseudometric-Space lzero lzero
pr1 pseudometric-space-ℚ = ℚ
pr2 pseudometric-space-ℚ =
  ( neighborhood-prop-ℚ ,
    is-reflexive-neighborhood-ℚ ,
    is-symmetric-neighborhood-ℚ ,
    is-triangular-neighborhood-ℚ ,
    is-saturated-neighborhood-ℚ)

abstract
  is-tight-pseudometric-space-ℚ :
    is-tight-Pseudometric-Space pseudometric-space-ℚ
  is-tight-pseudometric-space-ℚ x y H =
    antisymmetric-leq-ℚ
      ( x)
      ( y)
      ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ x y) (pr2 ∘ H))
      ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ y x) (pr1 ∘ H))

  is-extensional-pseudometric-space-ℚ :
    is-extensional-Pseudometric-Space pseudometric-space-ℚ
  is-extensional-pseudometric-space-ℚ =
    is-extensional-is-tight-Pseudometric-Space
      ( pseudometric-space-ℚ)
      ( is-tight-pseudometric-space-ℚ)
```

### The standard metric space of rational numbers

```agda
metric-space-ℚ : Metric-Space lzero lzero
metric-space-ℚ =
  make-Metric-Space
    ( ℚ)
    ( neighborhood-prop-ℚ)
    ( is-reflexive-neighborhood-ℚ)
    ( is-symmetric-neighborhood-ℚ)
    ( is-triangular-neighborhood-ℚ)
    ( is-saturated-neighborhood-ℚ)
    ( is-extensional-pseudometric-space-ℚ)
```

## Properties

### Relationship to the distance on rational numbers

```agda
abstract
  leq-dist-neighborhood-ℚ :
    (ε : ℚ⁺) (p q : ℚ) →
    neighborhood-ℚ ε p q →
    leq-ℚ (rational-dist-ℚ p q) (rational-ℚ⁺ ε)
  leq-dist-neighborhood-ℚ ε⁺@(ε , _) p q (H , K) =
    leq-dist-leq-diff-ℚ
      ( p)
      ( q)
      ( ε)
      ( swap-right-diff-leq-ℚ p ε q (leq-transpose-right-add-ℚ p q ε K))
      ( swap-right-diff-leq-ℚ q ε p (leq-transpose-right-add-ℚ q p ε H))

  neighborhood-leq-dist-ℚ :
    (ε : ℚ⁺) (p q : ℚ) →
    leq-ℚ (rational-dist-ℚ p q) (rational-ℚ⁺ ε) →
    neighborhood-ℚ ε p q
  neighborhood-leq-dist-ℚ ε⁺@(ε , _) p q |p-q|≤ε =
    ( leq-transpose-left-diff-ℚ
      ( q)
      ( ε)
      ( p)
      ( swap-right-diff-leq-ℚ
        ( q)
        ( p)
        ( ε)
        ( transitive-leq-ℚ
          ( q -ℚ p)
          ( rational-dist-ℚ p q)
          ( ε)
          ( |p-q|≤ε)
          ( leq-reversed-diff-dist-ℚ p q)))) ,
    ( leq-transpose-left-diff-ℚ
      ( p)
      ( ε)
      ( q)
      ( swap-right-diff-leq-ℚ
        ( p)
        ( q)
        ( ε)
        ( transitive-leq-ℚ
          ( p -ℚ q)
          ( rational-dist-ℚ p q)
          ( ε)
          ( |p-q|≤ε)
          ( leq-diff-dist-ℚ p q))))

leq-dist-iff-neighborhood-ℚ :
  (ε : ℚ⁺) (p q : ℚ) →
  leq-ℚ (rational-dist-ℚ p q) (rational-ℚ⁺ ε) ↔
  neighborhood-ℚ ε p q
pr1 (leq-dist-iff-neighborhood-ℚ ε p q) = neighborhood-leq-dist-ℚ ε p q
pr2 (leq-dist-iff-neighborhood-ℚ ε p q) = leq-dist-neighborhood-ℚ ε p q
```

### Addition of rational numbers is an isometry

```agda
module _
  (x u v : ℚ) (d : ℚ⁺)
  where

  abstract
    preserves-lower-neighborhood-add-ℚ :
      lower-neighborhood-ℚ d u v →
      lower-neighborhood-ℚ d (x +ℚ u) (x +ℚ v)
    preserves-lower-neighborhood-add-ℚ H =
      inv-tr
        ( leq-ℚ (x +ℚ v))
        ( associative-add-ℚ x u (rational-ℚ⁺ d))
        ( preserves-leq-right-add-ℚ
          ( x)
          ( v)
          ( u +ℚ rational-ℚ⁺ d)
          ( H))

    reflects-lower-neighborhood-add-ℚ :
      lower-neighborhood-ℚ d (x +ℚ u) (x +ℚ v) →
      lower-neighborhood-ℚ d u v
    reflects-lower-neighborhood-add-ℚ =
      ( reflects-leq-right-add-ℚ x v (u +ℚ rational-ℚ⁺ d)) ∘
      ( tr (leq-ℚ (x +ℚ v)) (associative-add-ℚ x u (rational-ℚ⁺ d)))
```

```agda
module _
  (x : ℚ)
  where

  abstract
    is-isometry-add-ℚ :
      is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( add-ℚ x)
    is-isometry-add-ℚ d y z =
      pair
        ( map-product
          ( preserves-lower-neighborhood-add-ℚ x y z d)
          ( preserves-lower-neighborhood-add-ℚ x z y d))
        ( map-product
          ( reflects-lower-neighborhood-add-ℚ x y z d)
          ( reflects-lower-neighborhood-add-ℚ x z y d))

    is-isometry-add-ℚ' :
      is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( add-ℚ' x)
    is-isometry-add-ℚ' d y z =
      binary-tr
        ( λ u v → neighborhood-ℚ d y z ↔ neighborhood-ℚ d u v)
        ( commutative-add-ℚ x y)
        ( commutative-add-ℚ x z)
        ( is-isometry-add-ℚ d y z)

    is-uniformly-continuous-add-ℚ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( add-ℚ x)
    is-uniformly-continuous-add-ℚ =
      is-uniformly-continuous-map-is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( add-ℚ x)
        ( is-isometry-add-ℚ)

  uniformly-continuous-add-ℚ :
    uniformly-continuous-map-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℚ)
  uniformly-continuous-add-ℚ =
    ( add-ℚ x , is-uniformly-continuous-add-ℚ)
```

### Negation of rational numbers is an isometry

```agda
abstract
  is-isometry-neg-ℚ :
    is-isometry-Metric-Space metric-space-ℚ metric-space-ℚ neg-ℚ
  is-isometry-neg-ℚ d x y =
    logical-equivalence-reasoning
      neighborhood-ℚ d x y
      ↔ leq-ℚ (rational-dist-ℚ x y) (rational-ℚ⁺ d)
        by inv-iff (leq-dist-iff-neighborhood-ℚ d x y)
      ↔ leq-ℚ (rational-dist-ℚ (neg-ℚ x) (neg-ℚ y)) (rational-ℚ⁺ d)
        by
          iff-eq
            ( ap
              ( λ z → leq-ℚ-Prop z (rational-ℚ⁺ d))
              ( inv (ap rational-ℚ⁰⁺ (dist-neg-ℚ x y))))
      ↔ neighborhood-ℚ d (neg-ℚ x) (neg-ℚ y)
        by leq-dist-iff-neighborhood-ℚ _ _ _

  is-uniformly-continuous-neg-ℚ :
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℚ)
      ( neg-ℚ)
  is-uniformly-continuous-neg-ℚ =
    is-uniformly-continuous-map-is-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℚ)
      ( neg-ℚ)
      ( is-isometry-neg-ℚ)

uniformly-continuous-neg-ℚ :
  uniformly-continuous-map-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-ℚ)
uniformly-continuous-neg-ℚ = (neg-ℚ , is-uniformly-continuous-neg-ℚ)
```

### Subtracting from a fixed rational number is an isometry

```agda
module _
  (q : ℚ)
  where

  abstract
    is-isometry-diff-ℚ :
      is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( diff-ℚ q)
    is-isometry-diff-ℚ =
      is-isometry-comp-is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( add-ℚ q)
        ( neg-ℚ)
        ( is-isometry-add-ℚ q)
        ( is-isometry-neg-ℚ)

    is-uniformly-continuous-diff-ℚ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( diff-ℚ q)
    is-uniformly-continuous-diff-ℚ =
      is-uniformly-continuous-map-is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( diff-ℚ q)
        ( is-isometry-diff-ℚ)

  uniformly-continuous-diff-ℚ :
    uniformly-continuous-map-Metric-Space metric-space-ℚ metric-space-ℚ
  uniformly-continuous-diff-ℚ =
    ( diff-ℚ q , is-uniformly-continuous-diff-ℚ)
```

### Multiplication of rational numbers is Lipschitz

```agda
module _
  (x : ℚ)
  where

  abstract
    is-lipschitz-constant-succ-abs-mul-ℚ :
      is-lipschitz-constant-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x)
        ( positive-succ-ℚ⁰⁺ (abs-ℚ x))
    is-lipschitz-constant-succ-abs-mul-ℚ d y z H =
      neighborhood-leq-dist-ℚ
        ( positive-succ-ℚ⁰⁺ (abs-ℚ x) *ℚ⁺ d)
        ( x *ℚ y)
        ( x *ℚ z)
        ( tr
          ( λ q →
            leq-ℚ
              ( rational-ℚ⁰⁺ q)
              ( rational-ℚ⁺ (positive-succ-ℚ⁰⁺ (abs-ℚ x) *ℚ⁺ d)))
          ( left-distributive-abs-mul-dist-ℚ x y z)
          ( transitive-leq-ℚ
            ( rational-ℚ⁰⁺ (abs-ℚ x *ℚ⁰⁺ dist-ℚ y z))
            ( (succ-ℚ (rational-abs-ℚ x)) *ℚ (rational-dist-ℚ y z))
            ( rational-ℚ⁺ (positive-succ-ℚ⁰⁺ (abs-ℚ x) *ℚ⁺ d))
            ( preserves-leq-left-mul-ℚ⁺
              ( positive-succ-ℚ⁰⁺ (abs-ℚ x))
              ( rational-dist-ℚ y z)
              ( rational-ℚ⁺ d)
              ( leq-dist-neighborhood-ℚ d y z H))
            ( preserves-leq-right-mul-ℚ⁰⁺
              ( dist-ℚ y z)
              ( rational-abs-ℚ x)
              ( succ-ℚ (rational-abs-ℚ x))
              ( succ-leq-ℚ (rational-abs-ℚ x)))))

    lipschitz-constant-succ-abs-mul-ℚ :
      lipschitz-constant-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x)
    lipschitz-constant-succ-abs-mul-ℚ =
      ( positive-succ-ℚ⁰⁺ (abs-ℚ x)) ,
      ( is-lipschitz-constant-succ-abs-mul-ℚ)

    is-lipschitz-left-mul-ℚ :
      ( is-lipschitz-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x))
    is-lipschitz-left-mul-ℚ =
      unit-trunc-Prop lipschitz-constant-succ-abs-mul-ℚ

    is-lipschitz-right-mul-ℚ :
      ( is-lipschitz-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ' x))
    is-lipschitz-right-mul-ℚ =
      is-lipschitz-htpy-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x)
        ( mul-ℚ' x)
        ( commutative-mul-ℚ x)
        ( is-lipschitz-left-mul-ℚ)

    is-uniformly-continuous-left-mul-ℚ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x)
    is-uniformly-continuous-left-mul-ℚ =
      is-uniformly-continuous-is-lipschitz-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ x)
        ( is-lipschitz-left-mul-ℚ)

    is-uniformly-continuous-right-mul-ℚ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ' x)
    is-uniformly-continuous-right-mul-ℚ =
      is-uniformly-continuous-is-lipschitz-map-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℚ)
        ( mul-ℚ' x)
        ( is-lipschitz-right-mul-ℚ)

  uniformly-continuous-left-mul-ℚ :
    uniformly-continuous-map-Metric-Space metric-space-ℚ metric-space-ℚ
  uniformly-continuous-left-mul-ℚ =
    ( mul-ℚ x , is-uniformly-continuous-left-mul-ℚ)

  uniformly-continuous-right-mul-ℚ :
    uniformly-continuous-map-Metric-Space metric-space-ℚ metric-space-ℚ
  uniformly-continuous-right-mul-ℚ =
    ( mul-ℚ' x , is-uniformly-continuous-right-mul-ℚ)
```

### The convergent Cauchy approximation of the canonical inclusion of positive rational numbers into the rational numbers

```agda
abstract
  is-cauchy-approximation-rational-ℚ⁺ :
    is-cauchy-approximation-Metric-Space
      metric-space-ℚ
      rational-ℚ⁺
  is-cauchy-approximation-rational-ℚ⁺ ε δ =
    ( leq-le-ℚ
      ( transitive-le-ℚ
        ( rational-ℚ⁺ δ)
        ( rational-ℚ⁺ (ε +ℚ⁺ δ))
        ( rational-ℚ⁺ ε +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
        ( le-right-add-ℚ⁺
          ( ε)
          ( ε +ℚ⁺ δ))
        ( le-right-add-ℚ⁺ ε δ))) ,
    ( leq-le-ℚ
      ( transitive-le-ℚ
        ( rational-ℚ⁺ ε)
        ( rational-ℚ⁺ (ε +ℚ⁺ δ))
        ( rational-ℚ⁺ δ +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
        ( le-right-add-ℚ⁺
          ( δ)
          ( ε +ℚ⁺ δ))
        ( le-left-add-ℚ⁺ ε δ)))

cauchy-approximation-rational-ℚ⁺ :
  cauchy-approximation-Metric-Space metric-space-ℚ
cauchy-approximation-rational-ℚ⁺ =
  rational-ℚ⁺ , is-cauchy-approximation-rational-ℚ⁺

abstract
  is-zero-limit-rational-ℚ⁺ :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-ℚ)
      ( cauchy-approximation-rational-ℚ⁺)
      ( zero-ℚ)
  is-zero-limit-rational-ℚ⁺ ε δ =
    ( leq-le-ℚ
      { zero-ℚ}
      { rational-ℚ⁺ (ε +ℚ⁺ (ε +ℚ⁺ δ))}
      ( le-zero-is-positive-ℚ
        ( is-positive-rational-ℚ⁺ (ε +ℚ⁺ (ε +ℚ⁺ δ))))) ,
    ( leq-le-ℚ
      { rational-ℚ⁺ ε}
      { zero-ℚ +ℚ rational-ℚ⁺ (ε +ℚ⁺ δ)}
      ( inv-tr
        ( le-ℚ (rational-ℚ⁺ ε))
        ( left-unit-law-add-ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
        ( le-left-add-ℚ⁺ ε δ)))

convergent-rational-ℚ⁺ :
  convergent-cauchy-approximation-Metric-Space metric-space-ℚ
convergent-rational-ℚ⁺ =
  cauchy-approximation-rational-ℚ⁺ ,
  zero-ℚ ,
  is-zero-limit-rational-ℚ⁺
```
