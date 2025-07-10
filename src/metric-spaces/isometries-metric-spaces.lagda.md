# Isometries between metric spaces

```agda
module metric-spaces.isometries-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.sets
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is an
{{#concept "isometry" Disambiguation="between metric spaces" Agda=is-isometry-Metric-Space}}
if the [rational neighborhood relation](metric-spaces.rational-neighborhoods.md)
on `A` is equivalent to the
[preimage](metric-spaces.preimage-rational-neighborhoods.md) by `f` of the
rational neighborhood relation on `B`. I.e., upper bounds on the distance
between two points in `A` are exactly the upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a isometry between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : type-function-Metric-Space A B)
  where

  is-isometry-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Metric-Space =
    Eq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Metric-Space A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Metric-Space B))

  is-isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Metric-Space =
    type-Prop is-isometry-prop-Metric-Space

  is-prop-is-isometry-Metric-Space :
    is-prop is-isometry-Metric-Space
  is-prop-is-isometry-Metric-Space =
    is-prop-type-Prop is-isometry-prop-Metric-Space
```

### The set of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  set-isometry-Metric-Space : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-isometry-Metric-Space =
    set-subset
      ( set-function-Metric-Space A B)
      ( is-isometry-prop-Metric-Space A B)

  isometry-Metric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Metric-Space = type-Set set-isometry-Metric-Space

  is-set-isometry-Metric-Space : is-set isometry-Metric-Space
  is-set-isometry-Metric-Space =
    is-set-type-Set set-isometry-Metric-Space

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  map-isometry-Metric-Space : type-function-Metric-Space A B
  map-isometry-Metric-Space = pr1 f

  is-isometry-map-isometry-Metric-Space :
    is-isometry-Metric-Space A B map-isometry-Metric-Space
  is-isometry-map-isometry-Metric-Space = pr2 f
```

## Properties

### The identity function on a metric space is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-isometry-id-Metric-Space :
    is-isometry-Metric-Space A A (λ x → x)
  is-isometry-id-Metric-Space d x y = id-iff

  isometry-id-Metric-Space : isometry-Metric-Space A A
  isometry-id-Metric-Space =
    (λ x → x) , is-isometry-id-Metric-Space
```

### Equality of isometries in metric spaces is equivalent to homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f g : isometry-Metric-Space A B)
  where

  equiv-eq-htpy-map-isometry-Metric-Space :
    (f ＝ g) ≃
    (map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g)
  equiv-eq-htpy-map-isometry-Metric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-isometry-prop-Metric-Space A B)
      ( f)
      ( g)

  htpy-eq-map-isometry-Metric-Space :
    (f ＝ g) →
    (map-isometry-Metric-Space A B f ~ map-isometry-Metric-Space A B g)
  htpy-eq-map-isometry-Metric-Space =
    map-equiv equiv-eq-htpy-map-isometry-Metric-Space

  eq-htpy-map-isometry-Metric-Space :
    ( map-isometry-Metric-Space A B f ~
      map-isometry-Metric-Space A B g) →
    (f ＝ g)
  eq-htpy-map-isometry-Metric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Metric-Space
```

### An isometry preserves and reflects neighborhoods

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  preserves-neighborhood-map-isometry-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space A) →
    neighborhood-Metric-Space A d x y →
    neighborhood-Metric-Space
      ( B)
      ( d)
      ( map-isometry-Metric-Space A B f x)
      ( map-isometry-Metric-Space A B f y)
  preserves-neighborhood-map-isometry-Metric-Space d x y =
    forward-implication
      ( is-isometry-map-isometry-Metric-Space A B f d x y)

  reflects-neighborhood-map-isometry-Metric-Space :
    (d : ℚ⁺) (x y : type-Metric-Space A) →
    neighborhood-Metric-Space
      ( B)
      ( d)
      ( map-isometry-Metric-Space A B f x)
      ( map-isometry-Metric-Space A B f y) →
    neighborhood-Metric-Space A d x y
  reflects-neighborhood-map-isometry-Metric-Space d x y =
    backward-implication
      ( is-isometry-map-isometry-Metric-Space A B f d x y)
```

### Composition of isometries

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  where

  is-isometry-comp-is-isometry-Metric-Space :
    (g : type-function-Metric-Space B C) →
    (f : type-function-Metric-Space A B) →
    is-isometry-Metric-Space B C g →
    is-isometry-Metric-Space A B f →
    is-isometry-Metric-Space A C (g ∘ f)
  is-isometry-comp-is-isometry-Metric-Space g f H K d x y =
    H d (f x) (f y) ∘iff K d x y

  comp-isometry-Metric-Space :
    isometry-Metric-Space B C →
    isometry-Metric-Space A B →
    isometry-Metric-Space A C
  comp-isometry-Metric-Space g f =
    ( map-isometry-Metric-Space B C g ∘
      map-isometry-Metric-Space A B f) ,
    ( is-isometry-comp-is-isometry-Metric-Space
      ( map-isometry-Metric-Space B C g)
      ( map-isometry-Metric-Space A B f)
      ( is-isometry-map-isometry-Metric-Space B C g)
      ( is-isometry-map-isometry-Metric-Space A B f))
```

### Unit laws for composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (f : isometry-Metric-Space A B)
  where

  left-unit-law-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A B B
      (isometry-id-Metric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-isometry-Metric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( A)
      ( B)
      ( comp-isometry-Metric-Space
        ( A)
        ( B)
        ( B)
        (isometry-id-Metric-Space B)
        ( f))
      ( f)
      ( λ x → refl)

  right-unit-law-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A A B
      ( f)
      ( isometry-id-Metric-Space A)) ＝
    ( f)
  right-unit-law-comp-isometry-Metric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( A)
      ( B)
      ( f)
      ( comp-isometry-Metric-Space
        ( A)
        ( A)
        ( B)
        ( f)
        ( isometry-id-Metric-Space A))
      ( λ x → refl)
```

### Associativity of composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (D : Metric-Space l1d l2d)
  (h : isometry-Metric-Space C D)
  (g : isometry-Metric-Space B C)
  (f : isometry-Metric-Space A B)
  where

  associative-comp-isometry-Metric-Space :
    ( comp-isometry-Metric-Space A B D
      ( comp-isometry-Metric-Space B C D h g)
      ( f)) ＝
    ( comp-isometry-Metric-Space A C D
      ( h)
      ( comp-isometry-Metric-Space A B C g f))
  associative-comp-isometry-Metric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( A)
      ( D)
      ( comp-isometry-Metric-Space A B D
        ( comp-isometry-Metric-Space B C D h g)
        ( f))
      ( comp-isometry-Metric-Space A C D
        ( h)
        ( comp-isometry-Metric-Space A B C g f))
      ( λ x → refl)
```

### The inverse of an isometric equivalence is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  where

  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space :
    (f : type-function-Metric-Space A B) →
    is-isometry-Metric-Space A B f →
    (E : is-equiv f) →
    is-isometry-Metric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space f I E d x y =
    logical-equivalence-reasoning
      ( neighborhood-Metric-Space B d x y)
      ↔ ( neighborhood-Metric-Space B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( neighborhood-Metric-Space B d x y) ↔
              ( neighborhood-Metric-Space B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( neighborhood-Metric-Space A d
          ( map-inv-is-equiv E x)
          ( map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  (E : is-equiv (map-isometry-Metric-Space A B f))
  where

  isometry-inv-is-equiv-isometry-Metric-Space :
    isometry-Metric-Space B A
  isometry-inv-is-equiv-isometry-Metric-Space =
    ( map-inv-is-equiv E) ,
    ( is-isometry-map-inv-is-equiv-is-isometry-Metric-Space
      ( A)
      ( B)
      ( map-isometry-Metric-Space A B f)
      ( is-isometry-map-isometry-Metric-Space A B f)
      ( E))

  is-section-isometry-inv-is-equiv-isometry-Metric-Space :
    ( comp-isometry-Metric-Space
      B
      A
      B
      f
      isometry-inv-is-equiv-isometry-Metric-Space) ＝
    ( isometry-id-Metric-Space B)
  is-section-isometry-inv-is-equiv-isometry-Metric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( B)
      ( B)
      ( comp-isometry-Metric-Space
        B
        A
        B
        f
        isometry-inv-is-equiv-isometry-Metric-Space)
      ( isometry-id-Metric-Space B)
      ( is-section-map-inv-is-equiv E)

  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space :
    ( comp-isometry-Metric-Space
      A
      B
      A
      isometry-inv-is-equiv-isometry-Metric-Space
      f) ＝
    ( isometry-id-Metric-Space A)
  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space =
    eq-htpy-map-isometry-Metric-Space
      ( A)
      ( A)
      ( comp-isometry-Metric-Space
        A
        B
        A
        isometry-inv-is-equiv-isometry-Metric-Space
        f)
      ( isometry-id-Metric-Space A)
      ( is-retraction-map-inv-is-equiv E)
```

### Any isometry between metric spaces is an embedding

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : isometry-Metric-Space A B)
  where

  is-injective-map-isometry-Metric-Space :
    is-injective (map-isometry-Metric-Space A B f)
  is-injective-map-isometry-Metric-Space H =
    eq-sim-Metric-Space
      ( A)
      ( _)
      ( _)
      ( λ d →
        backward-implication
          ( is-isometry-map-isometry-Metric-Space A B f d _ _)
          ( sim-eq-Metric-Space B _ _ H d))

  is-emb-map-isometry-Metric-Space :
    is-emb (map-isometry-Metric-Space A B f)
  is-emb-map-isometry-Metric-Space =
    is-emb-is-injective
      ( is-set-type-Metric-Space B)
      ( is-injective-map-isometry-Metric-Space)
```
