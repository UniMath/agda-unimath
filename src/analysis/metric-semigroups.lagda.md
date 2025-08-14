# Metric semigroups

```agda
module analysis.metric-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups

open import metric-spaces.metric-space-of-short-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A {{#concept "metric semigroup" Agda=Metric-Semigroup}} is a
[metric-space](metric-spaces.metric-spaces.md) equipped with a
[short](metric-spaces.short-functions-metric-spaces.md)
[associative binary operator](group-theory.semigroups.md).

## Definitions

### Associative short binary operators

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  mul-short-mul-Metric-Space :
    short-function-Metric-Space
      ( A)
      ( metric-space-of-short-functions-Metric-Space A A) →
    type-Metric-Space A →
    type-Metric-Space A →
    type-Metric-Space A
  mul-short-mul-Metric-Space f =
    ( map-short-function-Metric-Space A A) ∘
    ( map-short-function-Metric-Space
      ( A)
      ( metric-space-of-short-functions-Metric-Space A A)
      ( f))

  is-associative-prop-short-mul-Metric-Space :
    short-function-Metric-Space
      ( A)
      ( metric-space-of-short-functions-Metric-Space A A) →
    Prop l1
  is-associative-prop-short-mul-Metric-Space f =
    let
      μ : type-Metric-Space A → type-Metric-Space A → type-Metric-Space A
      μ = mul-short-mul-Metric-Space f
    in
      Π-Prop
        ( type-Metric-Space A)
        ( λ x →
          Π-Prop
            ( type-Metric-Space A)
            ( λ y →
              Π-Prop
                ( type-Metric-Space A)
                ( λ z →
                  Id-Prop
                    ( set-Metric-Space A)
                    ( μ (μ x y) z)
                    ( μ x (μ y z)))))
```

### Metric semigroups

```agda
Metric-Semigroup : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Metric-Semigroup l1 l2 =
  Σ ( Metric-Space l1 l2)
    ( type-subtype ∘ is-associative-prop-short-mul-Metric-Space)

module _
  {l1 l2 : Level} (M : Metric-Semigroup l1 l2)
  where

  metric-space-Metric-Semigroup : Metric-Space l1 l2
  metric-space-Metric-Semigroup = pr1 M

  set-Metric-Semigroup : Set l1
  set-Metric-Semigroup = set-Metric-Space metric-space-Metric-Semigroup

  type-Metric-Semigroup : UU l1
  type-Metric-Semigroup = type-Metric-Space metric-space-Metric-Semigroup

  short-associative-mul-Metric-Semigroup :
    type-subtype
      (is-associative-prop-short-mul-Metric-Space metric-space-Metric-Semigroup)
  short-associative-mul-Metric-Semigroup = pr2 M

  short-mul-Metric-Semigroup :
    short-function-Metric-Space
      ( metric-space-Metric-Semigroup)
      ( metric-space-of-short-functions-Metric-Space
        metric-space-Metric-Semigroup
        metric-space-Metric-Semigroup)
  short-mul-Metric-Semigroup = pr1 short-associative-mul-Metric-Semigroup

  mul-Metric-Semigroup :
    type-Metric-Semigroup → type-Metric-Semigroup → type-Metric-Semigroup
  mul-Metric-Semigroup =
    mul-short-mul-Metric-Space
      metric-space-Metric-Semigroup
      short-mul-Metric-Semigroup

  mul-Metric-Semigroup' :
    type-Metric-Semigroup → type-Metric-Semigroup → type-Metric-Semigroup
  mul-Metric-Semigroup' x y =
    mul-Metric-Semigroup y x

  associative-mul-Metric-Semigroup :
    (x y z : type-Metric-Semigroup) →
    mul-Metric-Semigroup (mul-Metric-Semigroup x y) z ＝
    mul-Metric-Semigroup x (mul-Metric-Semigroup y z)
  associative-mul-Metric-Semigroup =
    pr2 short-associative-mul-Metric-Semigroup

  semigroup-Metric-Semigroup : Semigroup l1
  semigroup-Metric-Semigroup =
    set-Metric-Semigroup ,
    mul-Metric-Semigroup ,
    associative-mul-Metric-Semigroup
```

## Properties

### Multiplication in a metric semigroup is short

```agda
module _
  {l1 l2 : Level} (M : Metric-Semigroup l1 l2) (x : type-Metric-Semigroup M)
  where

  is-short-mul-Metric-Semigroup :
    is-short-function-Metric-Space
      ( metric-space-Metric-Semigroup M)
      ( metric-space-Metric-Semigroup M)
      ( mul-Metric-Semigroup M x)
  is-short-mul-Metric-Semigroup =
    is-short-map-short-function-Metric-Space
      ( metric-space-Metric-Semigroup M)
      ( metric-space-Metric-Semigroup M)
      ( map-short-function-Metric-Space
        ( metric-space-Metric-Semigroup M)
        ( metric-space-of-short-functions-Metric-Space
          ( metric-space-Metric-Semigroup M)
          ( metric-space-Metric-Semigroup M))
          ( short-mul-Metric-Semigroup M)
          ( x))

  is-short-mul-Metric-Semigroup' :
    is-short-function-Metric-Space
      ( metric-space-Metric-Semigroup M)
      ( metric-space-Metric-Semigroup M)
      ( mul-Metric-Semigroup' M x)
  is-short-mul-Metric-Semigroup' d y z Nyz =
    is-short-map-short-function-Metric-Space
      ( metric-space-Metric-Semigroup M)
      ( metric-space-of-short-functions-Metric-Space
        ( metric-space-Metric-Semigroup M)
        ( metric-space-Metric-Semigroup M))
      ( short-mul-Metric-Semigroup M)
      ( d)
      ( y)
      ( z)
      ( Nyz)
      ( x)
```
