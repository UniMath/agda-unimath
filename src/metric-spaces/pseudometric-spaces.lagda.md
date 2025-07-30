# Pseudometric spaces

```agda
module metric-spaces.pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.discrete-premetric-structures
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A
{{#concept "pseudometric space" Agda=Pseudometric-Space WD="pseudometric space" WDID=Q1397059}}
is a [premetric space](metric-spaces.premetric-spaces.md) whose
[premetric](metric-spaces.premetric-structures.md) is a
[pseudometric](metric-spaces.pseudometric-structures.md): a
[reflexive](metric-spaces.reflexive-premetric-structures.md),
[symmetric](metric-spaces.symmetric-premetric-structures.md), and
[triangular](metric-spaces.triangular-premetric-structures.md) premetric.
Indistinguishability in a pseudometric space is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### The property of being a pseudometric premetric space

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-pseudometric-prop-Premetric-Space : Prop (l1 ⊔ l2)
  is-pseudometric-prop-Premetric-Space =
    is-pseudometric-prop-Premetric (structure-Premetric-Space A)

  is-pseudometric-Premetric-Space : UU (l1 ⊔ l2)
  is-pseudometric-Premetric-Space =
    type-Prop is-pseudometric-prop-Premetric-Space

  is-prop-is-pseudometric-Premetric-Space :
    is-prop is-pseudometric-Premetric-Space
  is-prop-is-pseudometric-Premetric-Space =
    is-prop-type-Prop is-pseudometric-prop-Premetric-Space
```

### The type of pseudometric spaces

```agda
Pseudometric-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Pseudometric-Space l1 l2 =
  type-subtype (is-pseudometric-prop-Premetric-Space {l1} {l2})

module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  premetric-Pseudometric-Space : Premetric-Space l1 l2
  premetric-Pseudometric-Space = pr1 M

  type-Pseudometric-Space : UU l1
  type-Pseudometric-Space =
    type-Premetric-Space premetric-Pseudometric-Space

  structure-Pseudometric-Space : Premetric l2 type-Pseudometric-Space
  structure-Pseudometric-Space =
    structure-Premetric-Space premetric-Pseudometric-Space

  neighborhood-Pseudometric-Space : ℚ⁺ → Relation l2 type-Pseudometric-Space
  neighborhood-Pseudometric-Space =
    neighborhood-Premetric-Space premetric-Pseudometric-Space

  is-prop-neighborhood-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space) →
    is-prop (neighborhood-Pseudometric-Space d x y)
  is-prop-neighborhood-Pseudometric-Space =
    is-prop-neighborhood-Premetric-Space premetric-Pseudometric-Space

  is-upper-bound-dist-Pseudometric-Space :
    (x y : type-Pseudometric-Space) (d : ℚ⁺) → UU l2
  is-upper-bound-dist-Pseudometric-Space =
    is-upper-bound-dist-Premetric-Space premetric-Pseudometric-Space

  is-pseudometric-structure-Pseudometric-Space :
    is-pseudometric-Premetric structure-Pseudometric-Space
  is-pseudometric-structure-Pseudometric-Space = pr2 M

  is-reflexive-structure-Pseudometric-Space :
    is-reflexive-Premetric structure-Pseudometric-Space
  is-reflexive-structure-Pseudometric-Space =
    is-reflexive-is-pseudometric-Premetric
      ( structure-Pseudometric-Space)
      ( is-pseudometric-structure-Pseudometric-Space)

  is-symmetric-structure-Pseudometric-Space :
    is-symmetric-Premetric structure-Pseudometric-Space
  is-symmetric-structure-Pseudometric-Space =
    is-symmetric-is-pseudometric-Premetric
      ( structure-Pseudometric-Space)
      ( is-pseudometric-structure-Pseudometric-Space)

  is-triangular-structure-Pseudometric-Space :
    is-triangular-Premetric structure-Pseudometric-Space
  is-triangular-structure-Pseudometric-Space =
    is-triangular-is-pseudometric-Premetric
      ( structure-Pseudometric-Space)
      ( is-pseudometric-structure-Pseudometric-Space)
```

### Indistinguishability in a pseudometric space

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  (x y : type-Pseudometric-Space M)
  where

  is-indistinguishable-prop-Pseudometric-Space : Prop l2
  is-indistinguishable-prop-Pseudometric-Space =
    is-indistinguishable-prop-Premetric (structure-Pseudometric-Space M) x y

  is-indistinguishable-Pseudometric-Space : UU l2
  is-indistinguishable-Pseudometric-Space =
    type-Prop is-indistinguishable-prop-Pseudometric-Space

  is-prop-is-indistinguishable-Pseudometric-Space :
    is-prop is-indistinguishable-Pseudometric-Space
  is-prop-is-indistinguishable-Pseudometric-Space =
    is-prop-type-Prop is-indistinguishable-prop-Pseudometric-Space
```

### The type of functions between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  map-type-Pseudometric-Space : UU (l1 ⊔ l1')
  map-type-Pseudometric-Space =
    type-Pseudometric-Space A → type-Pseudometric-Space B
```

## Properties

### Equal elements in a pseudometric space are indistinguishable

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  {x y : type-Pseudometric-Space M} (e : x ＝ y)
  where

  indistinguishable-eq-Pseudometric-Space :
    is-indistinguishable-Pseudometric-Space M x y
  indistinguishable-eq-Pseudometric-Space =
    indistinguishable-eq-reflexive-Premetric
      ( structure-Pseudometric-Space M)
      ( is-reflexive-structure-Pseudometric-Space M)
      ( e)
```

### Indistiguishability in a pseudometric space is an equivalence relation

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  is-equivalence-relation-is-indistinguishable-Pseudometric-Space :
    is-equivalence-relation
      (is-indistinguishable-prop-Pseudometric-Space M)
  is-equivalence-relation-is-indistinguishable-Pseudometric-Space =
    ( is-reflexive-is-indistinguishable-reflexive-Premetric
      ( structure-Pseudometric-Space M)
      ( is-reflexive-structure-Pseudometric-Space M)) ,
    ( is-symmetric-is-indistinguishable-is-symmetric-Premetric
      ( structure-Pseudometric-Space M)
      ( is-symmetric-structure-Pseudometric-Space M)) ,
    ( is-transitive-is-indistinguishable-triangular-Premetric
      ( structure-Pseudometric-Space M)
      ( is-triangular-structure-Pseudometric-Space M))
```

### Any type is a discrete pseudometric space

```agda
module _
  {l : Level} (A : UU l)
  where

  discrete-Pseudometric-Space : Pseudometric-Space l l
  pr1 discrete-Pseudometric-Space = discrete-Premetric-Space A
  pr2 discrete-Pseudometric-Space = is-pseudometric-discrete-Premetric
```

## See also

- Metric spaces are defined in
  [`metric-spaces.metric-spaces`](metric-spaces.metric-spaces.md).

## External links

- [metric space#variations](https://ncatlab.org/nlab/show/metric+space#variations)
  at $n$Lab
- [Pseudometric spaces](https://en.wikipedia.org/wiki/Pseudometric_space) at
  Wikipedia
