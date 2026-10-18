# Proper rational neighborhood subtypes

```agda
module metric-spaces.proper-rational-neighborhood-subtypes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-products-propositions
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.rational-neighborhood-subtypes
```

</details>

## Idea

A
[rational neighborhood subtype](metric-spaces.rational-neighborhood-subtypes.md)
`U : ℚ⁺ → subtype l A` is called
{{#concept "proper" Disambiguation="rational neighborhood subtype" Agda=is-proper-Rational-Neighborhood-Subtype}}
if it is [inhabited](foundation.inhabited-subtypes.md) for all radius `ε`:

```text
  ∀ (ε : ℚ⁺) → ∃ (x : A) (U ε x)
```

## Definitions

### Proper rational subtypes

```agda
module _
  {l1 l : Level} {A : UU l1} (U : Rational-Neighborhood-Subtype l A)
  where

  is-proper-prop-Rational-Neighborhood-Subtype : Prop (l1 ⊔ l)
  is-proper-prop-Rational-Neighborhood-Subtype =
    Π-Prop ℚ⁺ (is-inhabited-subtype-Prop ∘ U)

  is-proper-Rational-Neighborhood-Subtype : UU (l1 ⊔ l)
  is-proper-Rational-Neighborhood-Subtype =
    type-Prop is-proper-prop-Rational-Neighborhood-Subtype

  is-prop-is-proper-Rational-Neighborhood-Subtype :
    is-prop is-proper-Rational-Neighborhood-Subtype
  is-prop-is-proper-Rational-Neighborhood-Subtype =
    is-prop-type-Prop is-proper-prop-Rational-Neighborhood-Subtype
```
