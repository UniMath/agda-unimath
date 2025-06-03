# Short functions between premetric spaces

```agda
module metric-spaces.short-functions-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.isometries-premetric-spaces
open import metric-spaces.premetric-spaces
open import metric-spaces.uniformly-continuous-functions-premetric-spaces
```

</details>

## Idea

A function `f` between [premetric spaces](metric-spaces.premetric-spaces.md) is
{{#concept "short" Disambiguation="function between premetric spaces" Agda=is-short-function-Premetric-Space}}
if any of the following three [equivalent](foundation.logical-equivalences.md)
[propositions](foundation-core.propositions.md) holds:

- it maps [`d`-neighborhoods](metric-spaces.premetric-structures.md) to
  `d`-neighborhoods;
- any upper bound on the distance between two elements also bounds the distance
  between their image;
- the premetric on the domain of `f` is
  [finer](metric-spaces.ordering-premetric-structures.md) than the preimage of
  the metric on its codomain by `f`.

## Definitions

### The property of being a short function between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  where

  is-short-function-prop-Premetric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Premetric-Space =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( type-Premetric-Space A)
          ( λ x →
            Π-Prop
              ( type-Premetric-Space A)
              ( λ y →
                hom-Prop
                  ( structure-Premetric-Space A d x y)
                  ( structure-Premetric-Space B d (f x) (f y)))))

  is-short-function-Premetric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Premetric-Space =
    type-Prop is-short-function-prop-Premetric-Space

  is-prop-is-short-function-Premetric-Space :
    is-prop is-short-function-Premetric-Space
  is-prop-is-short-function-Premetric-Space =
    is-prop-type-Prop is-short-function-prop-Premetric-Space
```

### The type of short functions between premetric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  where

  short-function-Premetric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Premetric-Space =
    type-subtype (is-short-function-prop-Premetric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : short-function-Premetric-Space A B)
  where

  map-short-function-Premetric-Space :
    map-type-Premetric-Space A B
  map-short-function-Premetric-Space = pr1 f

  is-short-map-short-function-Premetric-Space :
    is-short-function-Premetric-Space A B map-short-function-Premetric-Space
  is-short-map-short-function-Premetric-Space = pr2 f
```

## Properties

### The identity function on a metric space is short

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space l1 l2)
  where

  is-short-id-Premetric-Space :
    is-short-function-Premetric-Space A A (id-Premetric-Space A)
  is-short-id-Premetric-Space d x y = id

  short-id-Premetric-Space : short-function-Premetric-Space A A
  short-id-Premetric-Space =
    id-Premetric-Space A , is-short-id-Premetric-Space
```

### Equality of short functions between premetric spaces is characterized by homotopy between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f g : short-function-Premetric-Space A B)
  where

  equiv-eq-htpy-map-short-function-Premetric-Space :
    ( f ＝ g) ≃
    ( map-short-function-Premetric-Space A B f ~
      map-short-function-Premetric-Space A B g)
  equiv-eq-htpy-map-short-function-Premetric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Premetric-Space A B) f g

  eq-htpy-map-short-function-Premetric-Space :
    ( map-short-function-Premetric-Space A B f ~
      map-short-function-Premetric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Premetric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-function-Premetric-Space
```

### Composition of short maps between premetric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Premetric-Space l1a l2a)
  (B : Premetric-Space l1b l2b)
  (C : Premetric-Space l1c l2c)
  (g : map-type-Premetric-Space B C)
  (f : map-type-Premetric-Space A B)
  where

  is-short-comp-function-Premetric-Space :
    is-short-function-Premetric-Space B C g →
    is-short-function-Premetric-Space A B f →
    is-short-function-Premetric-Space A C (g ∘ f)
  is-short-comp-function-Premetric-Space H K d x y =
    H d (f x) (f y) ∘ K d x y

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Premetric-Space l1a l2a)
  (B : Premetric-Space l1b l2b)
  (C : Premetric-Space l1c l2c)
  (g : short-function-Premetric-Space B C)
  (f : short-function-Premetric-Space A B)
  where

  comp-short-function-Premetric-Space : short-function-Premetric-Space A C
  pr1 comp-short-function-Premetric-Space =
    map-short-function-Premetric-Space B C g ∘
    map-short-function-Premetric-Space A B f
  pr2 comp-short-function-Premetric-Space =
    is-short-comp-function-Premetric-Space
      ( A)
      ( B)
      ( C)
      ( map-short-function-Premetric-Space B C g)
      ( map-short-function-Premetric-Space A B f)
      ( is-short-map-short-function-Premetric-Space B C g)
      ( is-short-map-short-function-Premetric-Space A B f)
```

### Any isometry between premetric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Premetric-Space l1 l2) (B : Premetric-Space l1' l2')
  (f : map-type-Premetric-Space A B)
  where

  is-short-is-isometry-Premetric-Space :
    is-isometry-Premetric-Space A B f →
    is-short-function-Premetric-Space A B f
  is-short-is-isometry-Premetric-Space H d x y =
    forward-implication (H d x y)
```

### Short maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Premetric-Space l1 l2) (B : Premetric-Space l3 l4)
  where

  is-uniformly-continuous-is-short-function-Premetric-Space :
    (f : map-type-Premetric-Space A B) →
    is-short-function-Premetric-Space A B f →
    is-uniformly-continuous-map-Premetric-Space A B f
  is-uniformly-continuous-is-short-function-Premetric-Space f H =
    intro-exists id (λ x ε → H ε x)
```

## External links

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
- [Metric maps](https://en.wikipedia.org/wiki/Metric_map) at Wikipedia
