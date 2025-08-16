# Reflexive rational neighborhood relations

```agda
module metric-spaces.reflexive-rational-neighborhood-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

A
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
is
{{#concept "reflexive" Disambiguation="rational neighborhood relation" Agda=is-reflexive-Rational-Neighborhood-Relation}}
if any element is in all neighborhoods of itself, i.e., if all `ε`-neighborhoods
are reflexive [binary relations](foundation.binary-relations.md).

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
