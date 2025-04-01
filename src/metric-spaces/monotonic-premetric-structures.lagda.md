# Monotonic premetric structures on types

```agda
module metric-spaces.monotonic-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.propositions
open import foundation.transport-along-identifications
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

  is-weakly-monotonic-Premetric : UU (l1 ⊔ l2)
  is-weakly-monotonic-Premetric =
    (x y : A) (d₁ d₂ : ℚ⁺) → leq-ℚ⁺ d₁ d₂ →
    type-Prop (B d₁ x y) → type-Prop (B d₂ x y)

  abstract
    is-weakly-monotonic-is-monotonic-Premetric :
      is-monotonic-Premetric → is-weakly-monotonic-Premetric
    is-weakly-monotonic-is-monotonic-Premetric H x y d₁ d₂ d₁≤d₂ x~y =
      rec-coproduct
        ( λ d₁<d₂ → H x y d₁ d₂ d₁<d₂ x~y)
        ( λ d₂≤d₁ →
          tr
            ( λ d → type-Prop (B d x y))
            ( eq-ℚ⁺
              { d₁}
              { d₂}
              ( antisymmetric-leq-ℚ
                ( rational-ℚ⁺ d₁)
                ( rational-ℚ⁺ d₂)
                ( d₁≤d₂)
                ( d₂≤d₁)))
            ( x~y))
        ( decide-le-leq-ℚ (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
```
