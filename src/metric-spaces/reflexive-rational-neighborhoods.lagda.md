# Reflexive rational neighborhoods on types

```agda
module metric-spaces.reflexive-rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

A [rational neighborhood](metric-spaces.rational-neighborhoods.md) is
{{#concept "reflexive" Disambiguation="premetric" Agda=is-reflexive-Rational-Neighborhood-Relation}}
if any element is in all neighborhoods of itself.

## Definitions

### The property of being a reflexive rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  is-reflexive-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-reflexive-prop-Rational-Neighborhood-Relation =
    Π-Prop ℚ⁺ (is-reflexive-prop-Relation-Prop ∘ B)

  is-reflexive-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-reflexive-Rational-Neighborhood-Relation =
    type-Prop is-reflexive-prop-Rational-Neighborhood-Relation

  is-prop-is-reflexive-Rational-Neighborhood-Relation :
    is-prop is-reflexive-Rational-Neighborhood-Relation
  is-prop-is-reflexive-Rational-Neighborhood-Relation =
    is-prop-type-Prop is-reflexive-prop-Rational-Neighborhood-Relation
```
