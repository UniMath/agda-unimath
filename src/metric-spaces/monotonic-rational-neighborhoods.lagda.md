# Monotonic rational neighborhoods on types

```agda
module metric-spaces.monotonic-rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

A [rational neighborhood relation](metric-spaces.rational-neighborhoods.md) is
{{#concept "monotonic" Disambiguation="rational neighborhood relation" Agda=is-monotonic-Rational-Neighborhood-Relation}}
if all `d₁`-neighborhoods are `d₂`-neighborhoods for `d₁ < d₂`.

## Definitions

### The property of being a monotonic rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  is-monotonic-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-monotonic-prop-Rational-Neighborhood-Relation =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( ℚ⁺)
              ( λ d₁ →
                ( Π-Prop
                  ( ℚ⁺)
                  ( λ d₂ →
                    ( Π-Prop
                      ( le-ℚ⁺ d₁ d₂)
                      ( λ H →
                        hom-Prop (B d₁ x y) (B d₂ x y))))))))))

  is-monotonic-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-monotonic-Rational-Neighborhood-Relation =
    type-Prop is-monotonic-prop-Rational-Neighborhood-Relation

  is-prop-is-monotonic-Rational-Neighborhood-Relation :
    is-prop is-monotonic-Rational-Neighborhood-Relation
  is-prop-is-monotonic-Rational-Neighborhood-Relation =
    is-prop-type-Prop is-monotonic-prop-Rational-Neighborhood-Relation
```
