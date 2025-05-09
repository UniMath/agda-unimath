# Similarity of elements in large premetric spaces

```agda
module metric-spaces.similarity-of-elements-large-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.large-premetric-spaces
open import metric-spaces.large-rational-neighborhoods
```

</details>

## Idea

Two elements `x y` of a
[large premetric space](metric-spaces.large-premetric-spaces.md) are
{{#concept "similar" Disambiguation="elements of a large premetric space" Agda=sim-element-Large-Premetric-Space}}
if their distance is bounded by all
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).
Similarity of element sin a large premetric space is reflexive, symmetric and
transitive.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  {l1 l2 : Level}
  (x : type-Large-Premetric-Space M l1)
  (y : type-Large-Premetric-Space M l2)
  where

  sim-prop-element-Large-Premetric-Space : Prop (β l1 l2)
  sim-prop-element-Large-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( is-upper-bound-dist-prop-Large-Premetric-Space M x y)

  sim-element-Large-Premetric-Space : UU (β l1 l2)
  sim-element-Large-Premetric-Space =
    type-Prop sim-prop-element-Large-Premetric-Space

  is-prop-sim-element-Large-Premetric-Space :
    is-prop sim-element-Large-Premetric-Space
  is-prop-sim-element-Large-Premetric-Space =
    is-prop-type-Prop sim-prop-element-Large-Premetric-Space
```

## Properties

### Similarity of elements in large premetric spaces is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  {l : Level} (x : type-Large-Premetric-Space M l)
  where

  sim-eq-element-Large-Premetric-Space :
    (y : type-Large-Premetric-Space M l) →
    x ＝ y →
    sim-element-Large-Premetric-Space M x y
  sim-eq-element-Large-Premetric-Space =
    neighborhood-eq-Large-Premetric-Space M x

  refl-sim-element-Large-Premetric-Space :
    sim-element-Large-Premetric-Space M x x
  refl-sim-element-Large-Premetric-Space =
    sim-eq-element-Large-Premetric-Space x refl
```

### Similarity of elements in large premetric spaces is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  where

  symmetric-sim-element-Large-Premetric-Space :
    {l1 l2 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2) →
    sim-element-Large-Premetric-Space M x y →
    sim-element-Large-Premetric-Space M y x
  symmetric-sim-element-Large-Premetric-Space x y x~y d =
    symmetric-neighborhood-Large-Premetric-Space M d x y (x~y d)

  inv-sim-element-Large-Premetric-Space :
    {l1 l2 : Level}
    {x : type-Large-Premetric-Space M l1}
    {y : type-Large-Premetric-Space M l2} →
    sim-element-Large-Premetric-Space M x y →
    sim-element-Large-Premetric-Space M y x
  inv-sim-element-Large-Premetric-Space {x = x} {y = y} =
    symmetric-sim-element-Large-Premetric-Space x y
```

### Similarity of elements in large premetric spaces is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (M : Large-Premetric-Space α β)
  where

  transitive-sim-element-Large-Premetric-Space :
    {l1 l2 l3 : Level}
    (x : type-Large-Premetric-Space M l1)
    (y : type-Large-Premetric-Space M l2)
    (z : type-Large-Premetric-Space M l3) →
    sim-element-Large-Premetric-Space M y z →
    sim-element-Large-Premetric-Space M x y →
    sim-element-Large-Premetric-Space M x z
  transitive-sim-element-Large-Premetric-Space x y z y~z x~y d =
    tr
      ( is-upper-bound-dist-Large-Premetric-Space M x z)
      ( eq-add-split-ℚ⁺ d)
      ( triangular-neighborhood-Large-Premetric-Space
        ( M)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( x)
        ( y)
        ( z)
        ( y~z (right-summand-split-ℚ⁺ d))
        ( x~y (left-summand-split-ℚ⁺ d)))
```
