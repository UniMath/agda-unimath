# Short functions between metric spaces

```agda
module metric-spaces.short-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-premetric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is
{{#concept "short" Disambiguation="function between metric spaces" Agda=is-short-function-Metric-Space}}
if it is [short](metric-spaces.short-functions-premetric-spaces.md) on their
carrier [premetric spaces](metric-spaces.premetric-spaces.md).

## Definitions

### The property of being a short function between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : function-carrier-type-Metric-Space A B)
  where

  is-short-function-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Metric-Space =
    is-short-function-prop-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)

  is-short-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Metric-Space =
    type-Prop is-short-function-prop-Metric-Space

  is-prop-is-short-function-Metric-Space :
    is-prop is-short-function-Metric-Space
  is-prop-is-short-function-Metric-Space =
    is-prop-type-Prop is-short-function-prop-Metric-Space
```

### The set of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  set-short-function-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-short-function-Metric-Space =
    set-subset
      ( set-function-carrier-type-Metric-Space A B)
      ( is-short-function-prop-Metric-Space A B)

  short-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Metric-Space = type-Set set-short-function-Metric-Space

  is-set-short-function-Metric-Space : is-set short-function-Metric-Space
  is-set-short-function-Metric-Space =
    is-set-type-Set set-short-function-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  where

  map-short-function-Metric-Space : function-carrier-type-Metric-Space A B
  map-short-function-Metric-Space =
    map-short-function-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)

  is-short-map-short-function-Metric-Space :
    is-short-function-Metric-Space A B map-short-function-Metric-Space
  is-short-map-short-function-Metric-Space =
    is-short-map-short-function-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
```

## Properties

### The identity function on a metric space is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-short-id-Metric-Space :
    is-short-function-Metric-Space A A (id-Metric-Space A)
  is-short-id-Metric-Space d x y H = H

  short-id-Metric-Space : short-function-Metric-Space A A
  short-id-Metric-Space =
    id-Metric-Space A , is-short-id-Metric-Space
```

### Equality of short functions between metric spaces is equivalent to homtopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : short-function-Metric-Space A B)
  where

  equiv-eq-htpy-map-short-function-Metric-Space :
    ( f ＝ g) ≃
    ( map-short-function-Metric-Space A B f ~
      map-short-function-Metric-Space A B g)
  equiv-eq-htpy-map-short-function-Metric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Metric-Space A B) f g

  eq-htpy-map-short-function-Metric-Space :
    ( map-short-function-Metric-Space A B f ~
      map-short-function-Metric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-function-Metric-Space
```

### The short composition of short functions

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : short-function-Metric-Space B C)
  (f : short-function-Metric-Space A B)
  where

  comp-short-function-Metric-Space :
    short-function-Metric-Space A C
  pr1 comp-short-function-Metric-Space =
    map-short-function-Metric-Space B C g ∘
    map-short-function-Metric-Space A B f
  pr2 comp-short-function-Metric-Space =
    preserves-short-comp-function-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( premetric-Metric-Space C)
      ( map-short-function-Metric-Space B C g)
      ( map-short-function-Metric-Space A B f)
      ( is-short-map-short-function-Metric-Space B C g)
      ( is-short-map-short-function-Metric-Space A B f)
```

### Constant functions between metric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (b : type-Metric-Space B)
  where

  is-short-constant-function-Metric-Space :
    is-short-function-Metric-Space A B (λ _ → b)
  is-short-constant-function-Metric-Space ε x y H =
    is-reflexive-premetric-structure-Metric-Space B ε b
```

### Any isometry between metric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : function-carrier-type-Metric-Space A B)
  where

  is-short-is-isometry-Metric-Space :
    is-isometry-Metric-Space A B f →
    is-short-function-Metric-Space A B f
  is-short-is-isometry-Metric-Space =
    is-short-is-isometry-Premetric-Space
      ( premetric-Metric-Space A)
      ( premetric-Metric-Space B)
      ( f)
```

### The embedding of isometries of metric spaces into short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  short-isometry-Metric-Space :
    isometry-Metric-Space A B → short-function-Metric-Space A B
  short-isometry-Metric-Space f =
    map-isometry-Metric-Space A B f ,
    is-short-is-isometry-Metric-Space
      ( A)
      ( B)
      ( map-isometry-Metric-Space A B f)
      ( is-isometry-map-isometry-Metric-Space A B f)

  htpy-map-short-isometry-Metric-Space :
    (map-short-function-Metric-Space A B ∘ short-isometry-Metric-Space) ~
    (map-isometry-Metric-Space A B)
  htpy-map-short-isometry-Metric-Space f = refl

  is-emb-short-isometry-Metric-Space :
    is-emb short-isometry-Metric-Space
  is-emb-short-isometry-Metric-Space =
    is-emb-right-factor
      ( map-short-function-Metric-Space A B)
      ( short-isometry-Metric-Space)
      ( is-emb-inclusion-subtype (is-short-function-prop-Metric-Space A B))
      ( is-emb-htpy
        ( htpy-map-short-isometry-Metric-Space)
        ( is-emb-inclusion-subtype (is-isometry-prop-Metric-Space A B)))
```

## References

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
