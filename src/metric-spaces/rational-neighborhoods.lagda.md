# Rational neighborhood relations on types

```agda
module metric-spaces.rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "rational neighborhood relation" Agda=Rational-Neighborhood-Relation}}
is a type family of
[proposition-valued binary relations](foundation.binary-relations.md) indexed by
the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

## Definitions

### Premetric structures

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Rational-Neighborhood-Relation : UU (l1 ⊔ lsuc l2)
  Rational-Neighborhood-Relation = ℚ⁺ → Relation-Prop l2 A

module _
  {l1 l2 : Level} {A : UU l1} (B : Rational-Neighborhood-Relation l2 A)
  where

  neighborhood-Rational-Neighborhood-Relation :
    ℚ⁺ → Relation l2 A
  neighborhood-Rational-Neighborhood-Relation d x y =
    type-Prop (B d x y)

  is-prop-neighborhood-Rational-Neighborhood-Relation :
    (d : ℚ⁺) (x y : A) →
    is-prop (neighborhood-Rational-Neighborhood-Relation d x y)
  is-prop-neighborhood-Rational-Neighborhood-Relation d x y =
    is-prop-type-Prop (B d x y)
```
