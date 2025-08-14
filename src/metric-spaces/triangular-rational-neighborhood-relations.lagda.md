# Triangular rational neighborhood relations

```agda
module metric-spaces.triangular-rational-neighborhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.monotonic-rational-neighborhood-relations
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
```

</details>

## Idea

A
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
is
{{#concept "triangular" Disambiguation="rational neighborhood relation" agda=is-triangular-Rational-Neighborhood-Relation}}
if it is additively transitive, i.e., if any `d₂`-neighbor of a `d₁`-neighbor of
an element is its `d₁ + d₂`-neighbor.

## Definitions

### The property of being a triangular rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  is-triangular-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-triangular-prop-Rational-Neighborhood-Relation =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( A)
              ( λ z →
                Π-Prop
                  ( ℚ⁺)
                  ( λ d₁ →
                    ( Π-Prop
                      ( ℚ⁺)
                      ( λ d₂ →
                        hom-Prop
                          ( B d₂ y z)
                          ( hom-Prop
                            ( B d₁ x y)
                            ( B (d₁ +ℚ⁺ d₂) x z))))))))))

  is-triangular-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-triangular-Rational-Neighborhood-Relation =
    type-Prop is-triangular-prop-Rational-Neighborhood-Relation

  is-prop-is-triangular-Rational-Neighborhood-Relation :
    is-prop is-triangular-Rational-Neighborhood-Relation
  is-prop-is-triangular-Rational-Neighborhood-Relation =
    is-prop-type-Prop is-triangular-prop-Rational-Neighborhood-Relation
```

## Properties

### Any triangular reflexive rational neighborhood relation is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  (R : is-reflexive-Rational-Neighborhood-Relation B)
  (T : is-triangular-Rational-Neighborhood-Relation B)
  where

  is-monotonic-is-reflexive-triangular-Rational-Neighborhood-Relation :
    is-monotonic-Rational-Neighborhood-Relation B
  is-monotonic-is-reflexive-triangular-Rational-Neighborhood-Relation
    x y d₁ d₂ I H₁ =
    tr
      ( λ d → neighborhood-Rational-Neighborhood-Relation B d x y)
      ( right-diff-law-add-ℚ⁺ d₁ d₂ I)
      ( T x y y d₁ (le-diff-ℚ⁺ d₁ d₂ I) (R (le-diff-ℚ⁺ d₁ d₂ I) y) H₁)
```
