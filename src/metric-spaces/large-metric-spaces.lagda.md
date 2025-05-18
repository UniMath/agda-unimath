# Large metric spaces

```agda
module metric-spaces.large-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.large-premetric-spaces
open import metric-spaces.large-rational-neighborhoods
open import metric-spaces.similarity-of-elements-large-premetric-spaces
```

</details>

## Idea

A {{#concept "large metric space" Agda=Large-Metric-Space}} is a
[large premetric space](metric-spaces.large-premetric-spaces.md) where
[similarity](metric-spaces.similarity-of-elements-large-premetric-spaces.md) has
propositional fibers.

## Definitions

### Extensional large premetric spaces

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  where

  is-extensional-Large-Premetric-Space : UUω
  is-extensional-Large-Premetric-Space =
    {l1 l2 : Level} → (x : type-Large-Premetric-Space M l1) →
    is-prop
      ( Σ
        ( type-Large-Premetric-Space M l2)
        ( sim-element-Large-Premetric-Space M x))
```

### The type of large metric spaces

```agda
record
  Large-Metric-Space (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Metric-Space
  field
    premetric-space-Large-Metric-Space :
      Large-Premetric-Space α β
    is-extensional-Large-Metric-Space :
      is-extensional-Large-Premetric-Space (premetric-space-Large-Metric-Space)

open Large-Metric-Space public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Metric-Space α β)
  where

  type-Large-Metric-Space : (l : Level) → UU (α l)
  type-Large-Metric-Space =
    type-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)

  neighborhood-Large-Metric-Space :
    Large-Rational-Neighborhood-Relation β type-Large-Metric-Space
  neighborhood-Large-Metric-Space =
    neighborhood-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)

  is-in-neighborhood-Large-Metric-Space :
    (d : ℚ⁺) {l1 l2 : Level} →
    type-Large-Metric-Space l1 →
    type-Large-Metric-Space l2 →
    UU (β l1 l2)
  is-in-neighborhood-Large-Metric-Space =
    is-in-neighborhood-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)

  is-prop-is-in-neighborhood-Large-Metric-Space :
    (d : ℚ⁺) {l1 l2 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2) →
    is-prop (is-in-neighborhood-Large-Metric-Space d x y)
  is-prop-is-in-neighborhood-Large-Metric-Space =
    is-prop-is-in-neighborhood-Large-Rational-Neighborhood-Relation
      neighborhood-Large-Metric-Space

  is-upper-bound-dist-prop-Large-Metric-Space :
    {l1 l2 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2) →
    ℚ⁺ →
    Prop (β l1 l2)
  is-upper-bound-dist-prop-Large-Metric-Space x y d =
    neighborhood-Large-Metric-Space d x y

  is-upper-bound-dist-Large-Metric-Space :
    {l1 l2 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2) →
    ℚ⁺ →
    UU (β l1 l2)
  is-upper-bound-dist-Large-Metric-Space x y d =
    is-in-neighborhood-Large-Metric-Space d x y

  is-prop-is-upper-bound-dist-Large-Metric-Space :
    {l1 l2 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2) →
    (d : ℚ⁺) →
    is-prop (is-upper-bound-dist-Large-Metric-Space x y d)
  is-prop-is-upper-bound-dist-Large-Metric-Space x y d =
    is-prop-is-in-neighborhood-Large-Metric-Space d x y

  refl-neighborhood-Large-Metric-Space :
    (d : ℚ⁺) {l : Level} (x : type-Large-Metric-Space l) →
    is-in-neighborhood-Large-Metric-Space d x x
  refl-neighborhood-Large-Metric-Space =
    refl-neighborhood-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)

  symmetric-neighborhood-Large-Metric-Space :
    (d : ℚ⁺) {l1 l2 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2) →
    is-in-neighborhood-Large-Metric-Space d x y →
    is-in-neighborhood-Large-Metric-Space d y x
  symmetric-neighborhood-Large-Metric-Space =
    symmetric-neighborhood-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)

  inv-neighborhood-Large-Metric-Space :
    (d : ℚ⁺) {l1 l2 : Level}
    {x : type-Large-Metric-Space l1}
    {y : type-Large-Metric-Space l2} →
    is-in-neighborhood-Large-Metric-Space d x y →
    is-in-neighborhood-Large-Metric-Space d y x
  inv-neighborhood-Large-Metric-Space d {x = x} {y = y} =
    symmetric-neighborhood-Large-Metric-Space d x y

  triangular-neighborhood-Large-Metric-Space :
    (ε δ : ℚ⁺) {l1 l2 l3 : Level}
    (x : type-Large-Metric-Space l1)
    (y : type-Large-Metric-Space l2)
    (z : type-Large-Metric-Space l3) →
    is-in-neighborhood-Large-Metric-Space δ y z →
    is-in-neighborhood-Large-Metric-Space ε x y →
    is-in-neighborhood-Large-Metric-Space (ε +ℚ⁺ δ) x z
  triangular-neighborhood-Large-Metric-Space =
    triangular-neighborhood-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)
```

## Properties

### Equal elements of a large metric space are neighors

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Metric-Space α β)
  where

  neighborhood-eq-Large-Metric-Space :
    {l : Level} (x y : type-Large-Metric-Space M l) →
    (x ＝ y) →
    (d : ℚ⁺) →
    is-in-neighborhood-Large-Metric-Space M d x y
  neighborhood-eq-Large-Metric-Space =
    neighborhood-eq-Large-Premetric-Space
      ( premetric-space-Large-Metric-Space M)
```
