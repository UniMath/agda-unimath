# The standard metric structure on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-space-of-rational-numbers where
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
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.premetric-structures
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with the [premetric](metric-spaces.premetric-structures.md) where
`x y : ℚ` are `d`-close when `y < x + d` and `x < y + d` is a
[metric space](metric-spaces.metric-spaces.md).

It is the
{{#concept "standard metric space of rational numbers" Agda=metric-space-ℚ}}

## Definitions

### The standard premetric on the rational numbers

```agda
premetric-ℚ : Premetric lzero ℚ
premetric-ℚ d x y =
  product-Prop
    ( le-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d)))
    ( le-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d)))
```

## Properties

### The standard premetric on the rational-numbers is a metric structure

```agda
is-reflexive-premetric-ℚ : is-reflexive-Premetric premetric-ℚ
is-reflexive-premetric-ℚ d x =
  (le-right-add-rational-ℚ⁺ x d , le-right-add-rational-ℚ⁺ x d)

is-symmetric-premetric-ℚ : is-symmetric-Premetric premetric-ℚ
is-symmetric-premetric-ℚ d x y (H , K) = (K , H)

is-tight-premetric-ℚ : is-tight-Premetric premetric-ℚ
is-tight-premetric-ℚ x y H =
  trichotomy-le-ℚ x y
    ( λ K →
      ex-falso
        ( irreflexive-le-ℚ
          ( y)
          ( tr
            ( le-ℚ y)
            ( ( commutative-add-ℚ x (y -ℚ x)) ∙
              ( associative-add-ℚ y (neg-ℚ x) x) ∙
              ( ap (y +ℚ_) (left-inverse-law-add-ℚ x) ∙
              ( right-unit-law-add-ℚ y)))
            ( pr1 (H ( y -ℚ x , is-positive-diff-le-ℚ x y K))))))
    ( id)
    ( λ K →
      ex-falso
        ( irreflexive-le-ℚ
          ( x)
          ( tr
            ( le-ℚ x)
            ( ( commutative-add-ℚ y (x -ℚ y)) ∙
              ( associative-add-ℚ x (neg-ℚ y) y) ∙
              ( ap (x +ℚ_) (left-inverse-law-add-ℚ y) ∙
              ( right-unit-law-add-ℚ x)))
            ( pr2 (H ( x -ℚ y , is-positive-diff-le-ℚ y x K))))))

is-local-premetric-ℚ : is-local-Premetric premetric-ℚ
is-local-premetric-ℚ =
  is-local-is-tight-Premetric
    premetric-ℚ
    is-tight-premetric-ℚ

is-triangular-premetric-ℚ :
  is-triangular-Premetric premetric-ℚ
pr1 (is-triangular-premetric-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( le-ℚ z)
    ( associative-add-ℚ x (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
    ( transitive-le-ℚ
      ( z)
      ( y +ℚ ( rational-ℚ⁺ d₂))
      ( x +ℚ (rational-ℚ⁺ d₁) +ℚ (rational-ℚ⁺ d₂))
      ( preserves-le-left-add-ℚ
        ( rational-ℚ⁺ d₂)
        ( y)
        ( x +ℚ (rational-ℚ⁺ d₁))
        ( pr1 Hxy))
      ( pr1 Hyz))
pr2 (is-triangular-premetric-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( le-ℚ x)
    ( ap (z +ℚ_) (commutative-add-ℚ (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁)))
    ( tr
      ( le-ℚ x)
      ( associative-add-ℚ z (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁))
      ( transitive-le-ℚ
        ( x)
        ( y +ℚ (rational-ℚ⁺ d₁))
        ( z +ℚ (rational-ℚ⁺ d₂) +ℚ (rational-ℚ⁺ d₁))
        ( ( preserves-le-left-add-ℚ
          ( rational-ℚ⁺ d₁)
          ( y)
          ( z +ℚ (rational-ℚ⁺ d₂))
          ( pr2 Hyz)))
        ( pr2 Hxy)))
```

### The standard metric space of rational numbers

```agda
metric-space-ℚ : Metric-Space lzero lzero
pr1 metric-space-ℚ = ℚ , premetric-ℚ
pr2 metric-space-ℚ =
  is-reflexive-premetric-ℚ ,
  is-symmetric-premetric-ℚ ,
  is-local-premetric-ℚ ,
  is-triangular-premetric-ℚ
```
