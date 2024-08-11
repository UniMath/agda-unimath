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
open import metric-spaces.neighbourhood-relations
```

</details>

## Idea

The
{{#concept "standard metric structure" Disambiguation="on the rational numbers" Agda=metric-structure-ℚ}}
on the [rational numbers](elementary-number-theory.rational-numbers.md) is the
[metric structure](metric-spaces.metric-spaces.md) where
[`d`-neighbourhoods](metric-spaces.neighbourhood-relations.md) are pairs
`x y : ℚ` such that `x < y + d` and `y < x + d`.

## Definitions

### The standard neighbourhood-relation on the rational numbers

```agda
neighbourhood-ℚ : neighbourhood-Relation-Prop lzero ℚ
neighbourhood-ℚ d x y =
  product-Prop
    ( le-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d)))
    ( le-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d)))
```

### The standard neighbourhood-relation on the rational-numbers is a metric structure

```agda
is-symmetric-neighbourhood-ℚ : is-symmetric-neighbourhood neighbourhood-ℚ
is-symmetric-neighbourhood-ℚ d x y (H , K) = (K , H)

is-reflexive-neighbourhood-ℚ : is-reflexive-neighbourhood neighbourhood-ℚ
is-reflexive-neighbourhood-ℚ d x =
  (le-right-add-rational-ℚ⁺ x d , le-right-add-rational-ℚ⁺ x d)

is-tight-neighbourhood-ℚ : is-tight-neighbourhood neighbourhood-ℚ
is-tight-neighbourhood-ℚ x y H =
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

is-triangular-neighbourhood-ℚ :
  is-triangular-neighbourhood neighbourhood-ℚ
pr1 (is-triangular-neighbourhood-ℚ x y z d₁ d₂ Hyz Hxy) =
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
pr2 (is-triangular-neighbourhood-ℚ x y z d₁ d₂ Hyz Hxy) =
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

is-metric-neighbourhood-ℚ : is-metric-neighbourhood ℚ-Set neighbourhood-ℚ
is-metric-neighbourhood-ℚ =
  is-symmetric-neighbourhood-ℚ ,
  is-reflexive-neighbourhood-ℚ ,
  is-tight-neighbourhood-ℚ ,
  is-triangular-neighbourhood-ℚ

metric-structure-ℚ : Metric-Structure lzero ℚ-Set
pr1 metric-structure-ℚ = neighbourhood-ℚ
pr2 metric-structure-ℚ = is-metric-neighbourhood-ℚ
```

### The standard metric space of rational numbers

```agda
metric-space-ℚ : Metric-Space lzero
pr1 metric-space-ℚ = ℚ-Set
pr2 metric-space-ℚ = metric-structure-ℚ
```
