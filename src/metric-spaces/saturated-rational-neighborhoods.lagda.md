# Saturated rational neighborhood relations

```agda
module metric-spaces.saturated-rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.monotonic-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

A [rational neighborhood relation](metric-spaces.rational-neighborhoods.md) on a
type `A` is
{{#concept "saturated" Disambiguation="rational neighborhood relation" Agda=is-saturated-Rational-Neighborhood-Relation}}
if `ε`-neighborhoods satisfy the following condition:

- For any `x y : A`, if `x` and `y` are in a `(ε + δ)`-neighborhood for all
  [positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
  `δ`, then they are in a `ε`-neighborhood.

Or, equivalently if for any `(x y : A)`, the subset of
[upper bounds](metric-spaces.rational-neighborhoods.md) on the distance between
`x` and `y` is closed on the left:

- For any `ε : ℚ⁺`, if `ε + δ` is an upper bound of the distance between `x` and
  `y` for all `(δ : ℚ⁺)`, then so is `ε`.

## Definitions

### The property of being a saturated rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  is-saturated-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-saturated-prop-Rational-Neighborhood-Relation =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
        ( A)
        ( λ x →
          Π-Prop
            ( A)
            ( λ y →
              hom-Prop
                ( Π-Prop
                  ( ℚ⁺)
                  ( λ δ → N (ε +ℚ⁺ δ) x y))
                ( N ε x y))))

  is-saturated-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-saturated-Rational-Neighborhood-Relation =
    type-Prop is-saturated-prop-Rational-Neighborhood-Relation

  is-prop-is-saturated-Rational-Neighborhood-Relation :
    is-prop is-saturated-Rational-Neighborhood-Relation
  is-prop-is-saturated-Rational-Neighborhood-Relation =
    is-prop-type-Prop is-saturated-prop-Rational-Neighborhood-Relation
```

### The saturation of a rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  saturate-Rational-Neighborhood-Relation : Rational-Neighborhood-Relation l2 A
  saturate-Rational-Neighborhood-Relation ε x y =
    Π-Prop ℚ⁺ (λ δ → N (ε +ℚ⁺ δ) x y)
```

## Properties

### The saturation of a rational neighborhood relation is saturated

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  where

  is-saturated-saturate-Rational-Neighborhood-Relation :
    is-saturated-Rational-Neighborhood-Relation
      ( saturate-Rational-Neighborhood-Relation N)
  is-saturated-saturate-Rational-Neighborhood-Relation ε x y H δ =
    tr
      ( is-upper-bound-dist-Rational-Neighborhood-Relation N x y)
      ( ( associative-add-ℚ⁺
          ( ε)
          ( left-summand-split-ℚ⁺ δ)
          ( right-summand-split-ℚ⁺ δ)) ∙
        ( ap (add-ℚ⁺ ε) (eq-add-split-ℚ⁺ δ)))
      ( H (left-summand-split-ℚ⁺ δ) (right-summand-split-ℚ⁺ δ))
```

### In a monotonic saturated rational neighborhood relation, `N ε x y ⇔ (∀ δ → ε < δ → N δ x y)`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Rational-Neighborhood-Relation l2 A)
  (monotonic-N : is-monotonic-Rational-Neighborhood-Relation N)
  (saturated-N : is-saturated-Rational-Neighborhood-Relation N)
  where

  iff-le-neighborhood-saturated-monotonic-Rational-Neighborhood-Relation :
    ( ε : ℚ⁺) (x y : A) →
    ( neighborhood-Rational-Neighborhood-Relation N ε x y) ↔
    ( (δ : ℚ⁺) →
      le-ℚ⁺ ε δ →
      neighborhood-Rational-Neighborhood-Relation N δ x y)
  iff-le-neighborhood-saturated-monotonic-Rational-Neighborhood-Relation ε x y =
    ( λ Nxy δ ε<δ → monotonic-N x y ε δ ε<δ Nxy) ,
    ( λ H → saturated-N ε x y λ δ → H (ε +ℚ⁺ δ) (le-left-add-ℚ⁺ ε δ))
```
