# Elements at bounded distance in metric spaces

```agda
module metric-spaces.elements-at-bounded-distance-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.metric-spaces

open import order-theory.preorders
```

</details>

## Idea

Two elements `x y : A` of a [metric space](metric-spaces.metric-spaces.md) are
{{#concept "at bounded distance" Disambiguation="in a metric space" Agda=bounded-dist-Metric-Space}}
if there [exists](foundation.existential-quantification.md) some
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`δ : ℚ⁺` such that `x` and `y` share a `δ`-neighborhood in `A`. Being at bounded
distance in a metric space is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### The relation of being at bounded distance in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x y : type-Metric-Space A)
  where

  bounded-dist-prop-Metric-Space : Prop l2
  bounded-dist-prop-Metric-Space =
    ∃ ℚ⁺ (λ d → neighborhood-prop-Metric-Space A d x y)

  bounded-dist-Metric-Space : UU l2
  bounded-dist-Metric-Space =
    type-Prop bounded-dist-prop-Metric-Space

  is-prop-bounded-dist-Metric-Space :
    is-prop bounded-dist-Metric-Space
  is-prop-bounded-dist-Metric-Space =
    is-prop-type-Prop bounded-dist-prop-Metric-Space
```

### Elements at bounded distance relative to a given element in metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-Metric-Space A)
  where

  element-at-bounded-dist-Metric-Space : UU (l1 ⊔ l2)
  element-at-bounded-dist-Metric-Space =
    type-subtype (bounded-dist-prop-Metric-Space A x)

  value-element-at-bounded-dist-Metric-Space :
    element-at-bounded-dist-Metric-Space → type-Metric-Space A
  value-element-at-bounded-dist-Metric-Space = pr1

  bounded-dist-value-element-at-bounded-dist-Metric-Space :
    (H : element-at-bounded-dist-Metric-Space) →
    bounded-dist-Metric-Space
      ( A)
      ( x)
      ( value-element-at-bounded-dist-Metric-Space H)
  bounded-dist-value-element-at-bounded-dist-Metric-Space = pr2
```

## Properties

### Being at bounded distance in a metric space is reflexive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  refl-bounded-dist-Metric-Space :
    (x : type-Metric-Space A) → bounded-dist-Metric-Space A x x
  refl-bounded-dist-Metric-Space x =
    map-trunc-Prop
      ( λ d → d , refl-neighborhood-Metric-Space A d x)
      ( is-inhabited-ℚ⁺)
```

### Being at bounded distance in a metric space is symmetric

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  symmetric-bounded-dist-Metric-Space :
    (x y : type-Metric-Space A) →
    bounded-dist-Metric-Space A x y →
    bounded-dist-Metric-Space A y x
  symmetric-bounded-dist-Metric-Space x y =
    map-tot-exists
      ( λ d → symmetric-neighborhood-Metric-Space A d x y)
```

### Being at bounded distance in a metric space is transitive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  transitive-bounded-dist-Metric :
    (x y z : type-Metric-Space A) →
    bounded-dist-Metric-Space A y z →
    bounded-dist-Metric-Space A x y →
    bounded-dist-Metric-Space A x z
  transitive-bounded-dist-Metric x y z =
    map-binary-exists
      ( is-upper-bound-dist-Metric-Space A x z)
      ( λ dyz dxy → dxy +ℚ⁺ dyz)
      ( λ dyz dxy → triangular-neighborhood-Metric-Space A x y z dxy dyz)
```

### The preorder of elements at bounded distance in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  preorder-bounded-dist-Metric-Space : Preorder l1 l2
  preorder-bounded-dist-Metric-Space =
    ( type-Metric-Space A) ,
    ( bounded-dist-prop-Metric-Space A) ,
    ( refl-bounded-dist-Metric-Space A) ,
    ( transitive-bounded-dist-Metric A)
```

### Being at bounded distance in a metric space is an equivalence relation

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-equivalence-relation-bounded-dist-Metric-Space :
    is-equivalence-relation (bounded-dist-prop-Metric-Space A)
  is-equivalence-relation-bounded-dist-Metric-Space =
    ( refl-bounded-dist-Metric-Space A) ,
    ( symmetric-bounded-dist-Metric-Space A) ,
    ( transitive-bounded-dist-Metric A)

  equivalence-relation-bounded-dist-Metric-Space :
    equivalence-relation l2 (type-Metric-Space A)
  equivalence-relation-bounded-dist-Metric-Space =
    ( bounded-dist-prop-Metric-Space A) ,
    ( refl-bounded-dist-Metric-Space A) ,
    ( symmetric-bounded-dist-Metric-Space A) ,
    ( transitive-bounded-dist-Metric A)
```
