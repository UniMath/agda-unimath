# Neighbors in metric spaces

```agda
module metric-spaces.neighbors-metric-spaces where
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
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces

open import order-theory.preorders
```

</details>

## Idea

Two elements `x y : A` of a [metric-space](metric-spaces.metric-spaces.md) are
{{#concept "neighbors" Disambiguation="in a metric space" Agda=neighbor-Metric-Space}}
if they are in some neighborhood in `A`, i.e., if there
[exists](foundation.existential-quantification.md) some
[positive rational number](elementary-number-theory.positive-rational-numbers.md)
`δ : ℚ⁺` such that `x` and `y` are `δ`-neighbors in `A`. Being neighbors in a
metric space is an equivalence relation.

## Definitions

### The relation of being neighbors in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x y : type-Metric-Space A)
  where

  is-neighbor-prop-Metric-Space : Prop l2
  is-neighbor-prop-Metric-Space =
    ∃ ℚ⁺ (λ d → structure-Metric-Space A d x y)

  is-neighbor-Metric-Space : UU l2
  is-neighbor-Metric-Space = type-Prop is-neighbor-prop-Metric-Space

  is-prop-is-neighbor-Metric-Space :
    is-prop is-neighbor-Metric-Space
  is-prop-is-neighbor-Metric-Space =
    is-prop-type-Prop is-neighbor-prop-Metric-Space
```

### Neighbors in metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-Metric-Space A)
  where

  neighbor-Metric-Space : UU (l1 ⊔ l2)
  neighbor-Metric-Space =
    type-subtype (is-neighbor-prop-Metric-Space A x)

  elem-neighbor-Metric-Space :
    neighbor-Metric-Space → type-Metric-Space A
  elem-neighbor-Metric-Space = pr1

  is-neighbor-elem-neighbor-Metric-Space :
    (H : neighbor-Metric-Space) →
    is-neighbor-Metric-Space A x (elem-neighbor-Metric-Space H)
  is-neighbor-elem-neighbor-Metric-Space = pr2
```

## Properties

### Being neighbors in a metric space is reflexive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  refl-is-neighbor-Metric-Space :
    (x : type-Metric-Space A) → is-neighbor-Metric-Space A x x
  refl-is-neighbor-Metric-Space x =
    map-trunc-Prop
      ( λ d → d , refl-structure-Metric-Space A d x)
      ( is-inhabited-ℚ⁺)
```

### Being neighbors in a metric space is symmetric

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  symmetric-is-neighbor-Metric-Space :
    (x y : type-Metric-Space A) →
    is-neighbor-Metric-Space A x y →
    is-neighbor-Metric-Space A y x
  symmetric-is-neighbor-Metric-Space x y =
    map-trunc-Prop
      ( λ (d , Nxy) → d , is-symmetric-structure-Metric-Space A d x y Nxy)
```

### Being neighbors in a metric space is transitive

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  transitive-is-neighbor-Metric :
    (x y z : type-Metric-Space A) →
    is-neighbor-Metric-Space A y z →
    is-neighbor-Metric-Space A x y →
    is-neighbor-Metric-Space A x z
  transitive-is-neighbor-Metric x y z Nyz Nxy =
    do
      (dyz , Ndyz) ← Nyz
      (dxy , Ndxy) ← Nxy
      intro-exists
        ( dxy +ℚ⁺ dyz)
        ( is-triangular-structure-Metric-Space A x y z dxy dyz Ndyz Ndxy)
    where
      open
        do-syntax-trunc-Prop (is-neighbor-prop-Metric-Space A x z)
```

### The preorder of neigbors in a metric space

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  preorder-is-neighbor-Metric-Space : Preorder l1 l2
  preorder-is-neighbor-Metric-Space =
    ( type-Metric-Space A) ,
    ( is-neighbor-prop-Metric-Space A) ,
    ( refl-is-neighbor-Metric-Space A) ,
    ( transitive-is-neighbor-Metric A)
```

### Being neighbors in a metric space is an equivalence relation

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-equivalence-relation-is-neighbor-Metric-Space :
    is-equivalence-relation (is-neighbor-prop-Metric-Space A)
  is-equivalence-relation-is-neighbor-Metric-Space =
    ( refl-is-neighbor-Metric-Space A) ,
    ( symmetric-is-neibhbor-Metric-Space A) ,
    ( transitive-is-neighbor-Metric A)
```

## See also

- [Total metric spaces](metric-spaces.total-metric-spaces.md) are metric spaces
  where all elements are neighbors of each other.
