# Triangular premetric structures on types

```agda
module metric-spaces.triangular-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) is
{{#concept "triangular" Disambiguation="premetric" agda=is-triangular-Premetric}}
if it is additively transitive. I.e., if for any three elements `x`, `y`, and
`z`, the sum of an upper bound on the distance between `x` and `y` and an upper
bound on the distance between `y` and `z` bounds the distance between `x` and
`z`.

## Definitions

### The property of being a triangular premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-triangular-prop-Premetric : Prop (l1 ⊔ l2)
  is-triangular-prop-Premetric =
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

  is-triangular-Premetric : UU (l1 ⊔ l2)
  is-triangular-Premetric = type-Prop is-triangular-prop-Premetric

  is-prop-is-triangular-Premetric : is-prop is-triangular-Premetric
  is-prop-is-triangular-Premetric =
    is-prop-type-Prop is-triangular-prop-Premetric
```

## Properties

### Indistiguishability in a triangular premetric is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-triangular-Premetric B)
  where

  is-transitive-is-indistinguishable-triangular-Premetric :
    is-transitive (is-indistinguishable-Premetric B)
  is-transitive-is-indistinguishable-triangular-Premetric x y z H K d =
    tr
      ( λ h → neighborhood-Premetric B h x z)
      ( eq-add-split-ℚ⁺ d)
      ( T
        ( x)
        ( y)
        ( z)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( H (right-summand-split-ℚ⁺ d))
        ( K (left-summand-split-ℚ⁺ d)))
```

### Any triangular reflexive premetric is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (T : is-triangular-Premetric B)
  where

  is-monotonic-is-reflexive-triangular-Premetric : is-monotonic-Premetric B
  is-monotonic-is-reflexive-triangular-Premetric x y d₁ d₂ I H₁ =
    tr
      ( λ d → neighborhood-Premetric B d x y)
      ( right-diff-law-add-ℚ⁺ d₁ d₂ I)
      ( T x y y d₁ (le-diff-ℚ⁺ d₁ d₂ I) (R (le-diff-ℚ⁺ d₁ d₂ I) y) H₁)
```
