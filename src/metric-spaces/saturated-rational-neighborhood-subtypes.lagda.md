# Saturated rational neighborhood subtypes

```agda
module metric-spaces.saturated-rational-neighborhood-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.rational-neighborhood-subtypes
```

</details>

## Idea

A
[rational neighborhood subtype](metric-spaces.rational-neighborhood-subtypes.md)
`U : ℚ⁺ → subtype l A` is called
{{#concept "saturated" Disambiguation="rational neighborhood subtype" Agda=is-saturated-Rational-Neighborhood-Subtype}}
if for any radius `ε : ℚ⁺`, `U ε` contains the intersection of `U δ` for all
`ε < δ`: `∩ (ε < δ) Uδ ⊆ Uε`, or, equivalently, for any point `x : A`

```text
  (∀ (δ : ℚ⁺) → U (ε + δ) x) ⇒ U ε x
```

## Definitions

### Saturated rational neighborhood subtypes

```agda
module _
  {l1 l : Level} {A : UU l1} (U : Rational-Neighborhood-Subtype l A)
  where

  is-saturated-prop-Rational-Neighborhood-Subtype : Prop (l1 ⊔ l)
  is-saturated-prop-Rational-Neighborhood-Subtype =
    Π-Prop
      ( ℚ⁺ × A)
      ( λ (ε , x) → (Π-Prop ℚ⁺ (λ δ → U (ε +ℚ⁺ δ) x)) ⇒ (U ε x))

  is-saturated-Rational-Neighborhood-Subtype : UU (l1 ⊔ l)
  is-saturated-Rational-Neighborhood-Subtype =
    type-Prop is-saturated-prop-Rational-Neighborhood-Subtype

  is-prop-is-saturated-Rational-Neighborhood-Subtype :
    is-prop is-saturated-Rational-Neighborhood-Subtype
  is-prop-is-saturated-Rational-Neighborhood-Subtype =
    is-prop-type-Prop is-saturated-prop-Rational-Neighborhood-Subtype
```
