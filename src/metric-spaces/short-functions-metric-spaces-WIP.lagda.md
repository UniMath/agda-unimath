# Short functions between metric spaces (WIP)

```agda
module metric-spaces.short-functions-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
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

open import metric-spaces.isometries-metric-spaces-WIP
open import metric-spaces.metric-spaces-WIP
open import metric-spaces.ordering-rational-neighborhoods
open import metric-spaces.preimage-rational-neighborhoods
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between two
[metric spaces](metric-spaces.metric-spaces.md) `A` and `B` is
{{#concept "short" Disambiguation="function between metric spaces" Agda=is-short-function-Metric-Space-WIP WD="metric map" WDID=Q2713824}}
if the [rational neighborhood relation](metric-spaces.rational-neighborhoods.md)
on `A` is [finer](metric-spaces.ordering-rational-neighborhoods.md) than the
[preimage](metric-spaces.preimage-rational-neighborhoods.md) by `f` of the
rational neighborhood relation on `B`. I.e., upper bounds on the distance
between two points in `A` are upper bounds of the distance between their images
in `B`.

## Definitions

### The property of being a short function between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : type-function-Metric-Space-WIP A B)
  where

  is-short-function-prop-Metric-Space-WIP : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Metric-Space-WIP =
    leq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Metric-Space-WIP A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Metric-Space-WIP B))

  is-short-function-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Metric-Space-WIP =
    type-Prop is-short-function-prop-Metric-Space-WIP

  is-prop-is-short-function-Metric-Space-WIP :
    is-prop is-short-function-Metric-Space-WIP
  is-prop-is-short-function-Metric-Space-WIP =
    is-prop-type-Prop is-short-function-prop-Metric-Space-WIP
```

### The set of short functions between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  where

  set-short-function-Metric-Space-WIP : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-short-function-Metric-Space-WIP =
    set-subset
      ( set-function-Metric-Space-WIP A B)
      ( is-short-function-prop-Metric-Space-WIP A B)

  short-function-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Metric-Space-WIP = type-Set set-short-function-Metric-Space-WIP

  is-set-short-function-Metric-Space-WIP :
    is-set short-function-Metric-Space-WIP
  is-set-short-function-Metric-Space-WIP =
    is-set-type-Set set-short-function-Metric-Space-WIP

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : short-function-Metric-Space-WIP A B)
  where

  map-short-function-Metric-Space-WIP : type-function-Metric-Space-WIP A B
  map-short-function-Metric-Space-WIP = pr1 f

  is-short-map-short-function-Metric-Space-WIP :
    is-short-function-Metric-Space-WIP A B map-short-function-Metric-Space-WIP
  is-short-map-short-function-Metric-Space-WIP = pr2 f
```

## Properties

### The identity function on a metric space is short

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  is-short-id-Metric-Space-WIP :
    is-short-function-Metric-Space-WIP A A (λ x → x)
  is-short-id-Metric-Space-WIP d x y H = H

  short-id-Metric-Space-WIP : short-function-Metric-Space-WIP A A
  short-id-Metric-Space-WIP =
    (λ x → x) , is-short-id-Metric-Space-WIP
```

### Equality of short functions between metric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f g : short-function-Metric-Space-WIP A B)
  where

  equiv-eq-htpy-map-short-function-Metric-Space-WIP :
    ( f ＝ g) ≃
    ( map-short-function-Metric-Space-WIP A B f ~
      map-short-function-Metric-Space-WIP A B g)
  equiv-eq-htpy-map-short-function-Metric-Space-WIP =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Metric-Space-WIP A B) f g

  eq-htpy-map-short-function-Metric-Space-WIP :
    ( map-short-function-Metric-Space-WIP A B f ~
      map-short-function-Metric-Space-WIP A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Metric-Space-WIP =
    map-inv-equiv equiv-eq-htpy-map-short-function-Metric-Space-WIP
```

### Composition of short functions

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (C : Metric-Space-WIP l1c l2c)
  where

  is-short-comp-is-short-function-Metric-Space-WIP :
    (g : type-function-Metric-Space-WIP B C) →
    (f : type-function-Metric-Space-WIP A B) →
    is-short-function-Metric-Space-WIP B C g →
    is-short-function-Metric-Space-WIP A B f →
    is-short-function-Metric-Space-WIP A C (g ∘ f)
  is-short-comp-is-short-function-Metric-Space-WIP g f H K d x y =
    H d (f x) (f y) ∘ K d x y

  comp-short-function-Metric-Space-WIP :
    short-function-Metric-Space-WIP B C →
    short-function-Metric-Space-WIP A B →
    short-function-Metric-Space-WIP A C
  comp-short-function-Metric-Space-WIP g f =
    ( map-short-function-Metric-Space-WIP B C g ∘
      map-short-function-Metric-Space-WIP A B f) ,
    ( is-short-comp-is-short-function-Metric-Space-WIP
      ( map-short-function-Metric-Space-WIP B C g)
      ( map-short-function-Metric-Space-WIP A B f)
      ( is-short-map-short-function-Metric-Space-WIP B C g)
      ( is-short-map-short-function-Metric-Space-WIP A B f))
```

### Unit laws for composition of short maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (f : short-function-Metric-Space-WIP A B)
  where

  left-unit-law-comp-short-function-Metric-Space-WIP :
    ( comp-short-function-Metric-Space-WIP A B B
      ( short-id-Metric-Space-WIP B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-short-function-Metric-Space-WIP =
    eq-htpy-map-short-function-Metric-Space-WIP
      ( A)
      ( B)
      ( comp-short-function-Metric-Space-WIP
        ( A)
        ( B)
        ( B)
        ( short-id-Metric-Space-WIP B)
        ( f))
      ( f)
      ( λ x → refl)

  right-unit-law-comp-short-function-Metric-Space-WIP :
    ( comp-short-function-Metric-Space-WIP A A B
      ( f)
      ( short-id-Metric-Space-WIP A)) ＝
    ( f)
  right-unit-law-comp-short-function-Metric-Space-WIP =
    eq-htpy-map-short-function-Metric-Space-WIP
      ( A)
      ( B)
      ( f)
      ( comp-short-function-Metric-Space-WIP
        ( A)
        ( A)
        ( B)
        ( f)
        ( short-id-Metric-Space-WIP A))
      ( λ x → refl)
```

### Associativity of composition of short maps between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (C : Metric-Space-WIP l1c l2c)
  (D : Metric-Space-WIP l1d l2d)
  (h : short-function-Metric-Space-WIP C D)
  (g : short-function-Metric-Space-WIP B C)
  (f : short-function-Metric-Space-WIP A B)
  where

  associative-comp-short-function-Metric-Space-WIP :
    ( comp-short-function-Metric-Space-WIP A B D
      ( comp-short-function-Metric-Space-WIP B C D h g)
        ( f)) ＝
    ( comp-short-function-Metric-Space-WIP A C D
      ( h)
      ( comp-short-function-Metric-Space-WIP A B C g f))
  associative-comp-short-function-Metric-Space-WIP =
    eq-htpy-map-short-function-Metric-Space-WIP
      ( A)
      ( D)
      ( comp-short-function-Metric-Space-WIP A B D
        ( comp-short-function-Metric-Space-WIP B C D h g)
        ( f))
      ( comp-short-function-Metric-Space-WIP A C D
        ( h)
        ( comp-short-function-Metric-Space-WIP A B C g f))
      ( λ x → refl)
```

### Constant functions between metric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (b : type-Metric-Space-WIP B)
  where

  is-short-constant-function-Metric-Space-WIP :
    is-short-function-Metric-Space-WIP A B (λ _ → b)
  is-short-constant-function-Metric-Space-WIP ε x y H =
    refl-neighborhood-Metric-Space-WIP B ε b
```

### Any isometry between metric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : type-function-Metric-Space-WIP A B)
  where

  is-short-is-isometry-Metric-Space-WIP :
    is-isometry-Metric-Space-WIP A B f →
    is-short-function-Metric-Space-WIP A B f
  is-short-is-isometry-Metric-Space-WIP I =
    preserves-neighborhood-map-isometry-Metric-Space-WIP A B (f , I)
```

### The embedding of isometries of metric spaces into short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  where

  short-isometry-Metric-Space-WIP :
    isometry-Metric-Space-WIP A B → short-function-Metric-Space-WIP A B
  short-isometry-Metric-Space-WIP f =
    map-isometry-Metric-Space-WIP A B f ,
    is-short-is-isometry-Metric-Space-WIP
      ( A)
      ( B)
      ( map-isometry-Metric-Space-WIP A B f)
      ( is-isometry-map-isometry-Metric-Space-WIP A B f)

  is-emb-short-isometry-Metric-Space-WIP :
    is-emb short-isometry-Metric-Space-WIP
  is-emb-short-isometry-Metric-Space-WIP =
    is-emb-right-factor
      ( map-short-function-Metric-Space-WIP A B)
      ( short-isometry-Metric-Space-WIP)
      ( is-emb-inclusion-subtype (is-short-function-prop-Metric-Space-WIP A B))
      ( is-emb-htpy
        ( λ f → refl)
        ( is-emb-inclusion-subtype (is-isometry-prop-Metric-Space-WIP A B)))

  emb-short-isometry-Metric-Space :
    isometry-Metric-Space-WIP A B ↪ short-function-Metric-Space-WIP A B
  emb-short-isometry-Metric-Space =
    short-isometry-Metric-Space-WIP ,
    is-emb-short-isometry-Metric-Space-WIP
```

### Short maps are uniformly continuous

```agda
-- module _
--   {l1 l2 l3 l4 : Level} (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l3 l4)
--   where

--   is-uniformly-continuous-is-short-function-Metric-Space-WIP :
--     (f : map-type-Metric-Space-WIP A B) → is-short-function-Metric-Space-WIP A B f →
--     is-uniformly-continuous-map-Metric-Space-WIP A B f
--   is-uniformly-continuous-is-short-function-Metric-Space-WIP =
--     is-uniformly-continuous-is-short-function-Premetric-Space
--       ( premetric-Metric-Space-WIP A)
--       ( premetric-Metric-Space-WIP B)
```

## See also

- The
  [category of short functions on metric spaces](metric-spaces.category-of-metric-spaces-and-short-functions.md)

## External links

- [Short maps](https://ncatlab.org/nlab/show/short+map) at $n$Lab
- [Metric maps](https://en.wikipedia.org/wiki/Metric_map) at Wikipedia
