# Monotonic premetric structures on types

```agda
module metric-spaces.monotonic-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) is
{{#concept "monotonic" Disambiguation="premetric" Agda=is-monotonic-Premetric}}
if any `d₁`-neighborhoods are `d₂`-neighborhoods for `d₁ < d₂`, i.e., if the
subsets of upper bounds on the distance between any two points are upper stable.

## Definitions

### The property of being a monotonic premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-monotonic-prop-Premetric : Prop (l1 ⊔ l2)
  is-monotonic-prop-Premetric =
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

  is-monotonic-Premetric : UU (l1 ⊔ l2)
  is-monotonic-Premetric = type-Prop is-monotonic-prop-Premetric

  is-prop-is-monotonic-Premetric : is-prop is-monotonic-Premetric
  is-prop-is-monotonic-Premetric = is-prop-type-Prop is-monotonic-prop-Premetric
```
