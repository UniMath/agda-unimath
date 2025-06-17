# Large rational neighborhoods on types

```agda
module metric-spaces.large-rational-neighborhoods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{concept "large rational neighborhood" Agda=Large-Rational-Neighborhood}} on
a family of types indexed by universe levels `A` is a family of
[large relations](foundation.large-binary-relations.md) on `A` indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

## Definitions

```agda
module _
  {α : Level → Level} (β : Level → Level → Level)
  (A : (l : Level) → UU (α l))
  where

  Large-Rational-Neighborhood-Relation : UUω
  Large-Rational-Neighborhood-Relation =
    ℚ⁺ → Large-Relation-Prop β A

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (N : Large-Rational-Neighborhood-Relation β A)
  (d : ℚ⁺) {l1 l2 : Level} (x : A l1) (y : A l2)
  where

  neighborhood-Large-Rational-Neighborhood-Relation : Prop (β l1 l2)
  neighborhood-Large-Rational-Neighborhood-Relation = N d x y

  is-in-neighborhood-Large-Rational-Neighborhood-Relation : UU (β l1 l2)
  is-in-neighborhood-Large-Rational-Neighborhood-Relation =
    type-Prop neighborhood-Large-Rational-Neighborhood-Relation

  is-prop-is-in-neighborhood-Large-Rational-Neighborhood-Relation :
    is-prop is-in-neighborhood-Large-Rational-Neighborhood-Relation
  is-prop-is-in-neighborhood-Large-Rational-Neighborhood-Relation =
    is-prop-type-Prop neighborhood-Large-Rational-Neighborhood-Relation
```

## Properties

### Specification of properties of rational neighborhoods

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (N : Large-Rational-Neighborhood-Relation β A)
  where

  is-reflexive-Large-Rational-Neighborhood-Relation : UUω
  is-reflexive-Large-Rational-Neighborhood-Relation =
    (d : ℚ⁺) {l : Level} (x : A l) →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N d x x

  is-symmetric-Large-Rational-Neighborhood-Relation : UUω
  is-symmetric-Large-Rational-Neighborhood-Relation =
    (d : ℚ⁺) {l1 l2 : Level} (x : A l1) (y : A l2) →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N d x y →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N d y x

  is-triangular-Large-Rational-Neighborhood-Relation : UUω
  is-triangular-Large-Rational-Neighborhood-Relation =
    (ε δ : ℚ⁺) {l1 l2 l3 : Level} (x : A l1) (y : A l2) (z : A l3) →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N δ y z →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N ε x y →
    is-in-neighborhood-Large-Rational-Neighborhood-Relation N (ε +ℚ⁺ δ) x z
```
