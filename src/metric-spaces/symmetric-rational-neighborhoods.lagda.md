# Symmetric rational neighborhoods on types

```agda
module metric-spaces.symmetric-rational-neighborhoods where
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

A [rational neighborhood relation](metric-spaces.rational-neighborhoods.md) is
{{#concept "symmetric" Disambiguation="rational neighborhood relation" Agda=is-symmetric-Rational-Neighborhood-Relation}}
if all `ε`-neighborhoods are symmetric
[binary relations](foundation.binary-relations.md).

## Definitions

### The property of being a symmetric rational neighborhood relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  is-symmetric-prop-Rational-Neighborhood-Relation : Prop (l1 ⊔ l2)
  is-symmetric-prop-Rational-Neighborhood-Relation =
    Π-Prop ℚ⁺ (is-symmetric-prop-Relation-Prop ∘ B)

  is-symmetric-Rational-Neighborhood-Relation : UU (l1 ⊔ l2)
  is-symmetric-Rational-Neighborhood-Relation =
    type-Prop is-symmetric-prop-Rational-Neighborhood-Relation

  is-prop-is-symmetric-Rational-Neighborhood-Relation :
    is-prop is-symmetric-Rational-Neighborhood-Relation
  is-prop-is-symmetric-Rational-Neighborhood-Relation =
    is-prop-type-Prop is-symmetric-prop-Rational-Neighborhood-Relation
```
