# Large premetric spaces

```agda
module metric-spaces.large-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.large-rational-neighborhoods
```

</details>

## Idea

A {{concept "large premetric space" Agda=Large-Premetric-Space}} is a family of
types indexed by universe levels equipped with a reflexive, symmetric and
triangular
[large rational neighborhood](metric-spaces.large-rational-neighborhoods.md).

## Definitions

```agda
record
  Large-Premetric-Space (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Premetric-Space
  field
    type-Large-Premetric-Space : (l : Level) → UU (α l)
    neighborhood-Large-Premetric-Space :
      Large-Rational-Neighborhood-Relation β type-Large-Premetric-Space
    refl-neighborhood-Large-Premetric-Space :
      is-reflexive-Large-Rational-Neighborhood-Relation
        neighborhood-Large-Premetric-Space
    symmetric-neighborhood-Large-Premetric-Space :
      is-symmetric-Large-Rational-Neighborhood-Relation
        neighborhood-Large-Premetric-Space
    triangular-neighborhood-Large-Premetric-Space :
      is-triangular-Large-Rational-Neighborhood-Relation
        neighborhood-Large-Premetric-Space

open Large-Premetric-Space public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  where

  is-in-neighborhood-Large-Premetric-Space :
    (d : ℚ⁺) {l1 l2 : Level} →
    type-Large-Premetric-Space M l1 →
    type-Large-Premetric-Space M l2 →
    UU (β l1 l2)
  is-in-neighborhood-Large-Premetric-Space =
    is-in-neighborhood-Large-Rational-Neighborhood-Relation
      (neighborhood-Large-Premetric-Space M)

  is-prop-is-in-neighborhood-Large-Premetric-Space :
    (d : ℚ⁺) {l1 l2 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2) →
    is-prop (is-in-neighborhood-Large-Premetric-Space d x y)
  is-prop-is-in-neighborhood-Large-Premetric-Space =
    is-prop-is-in-neighborhood-Large-Rational-Neighborhood-Relation
      (neighborhood-Large-Premetric-Space M)

  is-upper-bound-dist-prop-Large-Premetric-Space :
    {l1 l2 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2) →
    ℚ⁺ →
    Prop (β l1 l2)
  is-upper-bound-dist-prop-Large-Premetric-Space x y d =
    neighborhood-Large-Premetric-Space M d x y

  is-upper-bound-dist-Large-Premetric-Space :
    {l1 l2 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2) →
    ℚ⁺ →
    UU (β l1 l2)
  is-upper-bound-dist-Large-Premetric-Space x y d =
    is-in-neighborhood-Large-Premetric-Space d x y

  is-prop-is-upper-bound-dist-Large-Premetric-Space :
    {l1 l2 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2) →
    (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Large-Premetric-Space x y d)
  is-prop-is-upper-bound-dist-Large-Premetric-Space x y d =
    is-prop-is-in-neighborhood-Large-Premetric-Space d x y
```

## Properties

### Equal elements of a large premetric space are neighors

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  where

  neighborhood-eq-Large-Premetric-Space :
    {l : Level} (x y : type-Large-Premetric-Space M l) →
    (x ＝ y) →
    (d : ℚ⁺) →
    is-in-neighborhood-Large-Premetric-Space M d x y
  neighborhood-eq-Large-Premetric-Space x .x refl d =
    refl-neighborhood-Large-Premetric-Space M d x
```
