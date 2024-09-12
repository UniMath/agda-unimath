# The standard saturated metric structure on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.saturated-metric-space-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.local-premetric-structures
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with the [premetric](metric-spaces.premetric-structures.md) where
`x y : ℚ` are in `d`-neighborhood when `y ≤ x + d` and `x ≤ y + d` is a
[metric space](metric-spaces.metric-spaces.md).

Moreover, it is [saturated](metric-spaces.saturated-metric-spaces.md).

It is the
{{#concept "standard saturated metric space of rational numbers" Agda=metric-space-leq-ℚ}}

## Definitions

### The standard saturated premetric on the rational numbers

```agda
premetric-leq-ℚ : Premetric lzero ℚ
premetric-leq-ℚ d x y =
  product-Prop
    ( leq-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d)))
    ( leq-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d)))
```

## Properties

### The standard premetric on the rational numbers is a metric

```agda
is-reflexive-premetric-leq-ℚ : is-reflexive-Premetric premetric-leq-ℚ
is-reflexive-premetric-leq-ℚ d x = α , α
  where

  α : leq-ℚ x (x +ℚ (rational-ℚ⁺ d))
  α = leq-le-ℚ {x} {x +ℚ (rational-ℚ⁺ d)} (le-right-add-rational-ℚ⁺ x d)

is-symmetric-premetric-leq-ℚ : is-symmetric-Premetric premetric-leq-ℚ
is-symmetric-premetric-leq-ℚ d x y (H , K) = (K , H)

is-tight-premetric-leq-ℚ : is-tight-Premetric premetric-leq-ℚ
is-tight-premetric-leq-ℚ x y H =
  antisymmetric-leq-ℚ
    ( x)
    ( y)
    ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ x y) (pr2 ∘ H))
    ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ y x) (pr1 ∘ H))

is-local-premetric-leq-ℚ : is-local-Premetric premetric-leq-ℚ
is-local-premetric-leq-ℚ =
  is-local-is-tight-Premetric
    premetric-leq-ℚ
    is-tight-premetric-leq-ℚ

is-triangular-premetric-leq-ℚ :
  is-triangular-Premetric premetric-leq-ℚ
pr1 (is-triangular-premetric-leq-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( leq-ℚ z)
    ( associative-add-ℚ x (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
    ( transitive-leq-ℚ
      ( z)
      ( y +ℚ ( rational-ℚ⁺ d₂))
      ( x +ℚ (rational-ℚ⁺ d₁) +ℚ (rational-ℚ⁺ d₂))
      ( preserves-leq-left-add-ℚ
        ( rational-ℚ⁺ d₂)
        ( y)
        ( x +ℚ (rational-ℚ⁺ d₁))
        ( pr1 Hxy))
      ( pr1 Hyz))
pr2 (is-triangular-premetric-leq-ℚ x y z d₁ d₂ Hyz Hxy) =
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

is-pseudometric-premetric-leq-ℚ : is-pseudometric-Premetric premetric-leq-ℚ
is-pseudometric-premetric-leq-ℚ =
  is-reflexive-premetric-leq-ℚ ,
  is-symmetric-premetric-leq-ℚ ,
  is-triangular-premetric-leq-ℚ

is-metric-premetric-leq-ℚ : is-metric-Premetric premetric-leq-ℚ
pr1 is-metric-premetric-leq-ℚ = is-pseudometric-premetric-leq-ℚ
pr2 is-metric-premetric-leq-ℚ = is-local-premetric-leq-ℚ
```

### The standard saturated metric space of rational numbers

```agda
metric-space-leq-ℚ : Metric-Space lzero lzero
pr1 metric-space-leq-ℚ = ℚ , premetric-leq-ℚ
pr2 metric-space-leq-ℚ = is-metric-premetric-leq-ℚ
```

## Properties

### The standard saturated metric space of rationa numbers is saturated

```agda
is-saturated-metric-space-leq-ℚ :
  is-saturated-Metric-Space metric-space-leq-ℚ
is-saturated-metric-space-leq-ℚ ε x y H =
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
```
