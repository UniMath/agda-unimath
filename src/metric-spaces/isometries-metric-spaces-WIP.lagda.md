# Isometries between metric spaces (WIP)

```agda
module metric-spaces.isometries-metric-spaces-WIP where
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

open import metric-spaces.metric-spaces-WIP
open import metric-spaces.preimage-rational-neighborhoods
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) between
[metric spaces](metric-spaces.metric-spaces.md) is an
{{#concept "isometry" Disambiguation="between metric spaces" Agda=is-isometry-Metric-Space-WIP}}
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
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : type-function-Metric-Space-WIP A B)
  where

  is-isometry-prop-Metric-Space-WIP : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Metric-Space-WIP =
    Eq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Metric-Space-WIP A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Metric-Space-WIP B))

  is-isometry-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Metric-Space-WIP =
    type-Prop is-isometry-prop-Metric-Space-WIP

  is-prop-is-isometry-Metric-Space-WIP :
    is-prop is-isometry-Metric-Space-WIP
  is-prop-is-isometry-Metric-Space-WIP =
    is-prop-type-Prop is-isometry-prop-Metric-Space-WIP
```

### The set of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  where

  set-isometry-Metric-Space-WIP : Set (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  set-isometry-Metric-Space-WIP =
    set-subset
      ( set-function-Metric-Space-WIP A B)
      ( is-isometry-prop-Metric-Space-WIP A B)

  isometry-Metric-Space-WIP : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Metric-Space-WIP = type-Set set-isometry-Metric-Space-WIP

  is-set-isometry-Metric-Space-WIP : is-set isometry-Metric-Space-WIP
  is-set-isometry-Metric-Space-WIP =
    is-set-type-Set set-isometry-Metric-Space-WIP

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : isometry-Metric-Space-WIP A B)
  where

  map-isometry-Metric-Space-WIP : type-function-Metric-Space-WIP A B
  map-isometry-Metric-Space-WIP = pr1 f

  is-isometry-map-isometry-Metric-Space-WIP :
    is-isometry-Metric-Space-WIP A B map-isometry-Metric-Space-WIP
  is-isometry-map-isometry-Metric-Space-WIP = pr2 f
```

## Properties

### The identity function on a metric space is an isometry

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  is-isometry-id-Metric-Space-WIP :
    is-isometry-Metric-Space-WIP A A (λ x → x)
  is-isometry-id-Metric-Space-WIP d x y = id-iff

  isometry-id-Metric-Space-WIP : isometry-Metric-Space-WIP A A
  isometry-id-Metric-Space-WIP =
    (λ x → x) , is-isometry-id-Metric-Space-WIP
```

### Equality of isometries in metric spaces is equivalent to homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f g : isometry-Metric-Space-WIP A B)
  where

  equiv-eq-htpy-map-isometry-Metric-Space-WIP :
    (f ＝ g) ≃
    (map-isometry-Metric-Space-WIP A B f ~ map-isometry-Metric-Space-WIP A B g)
  equiv-eq-htpy-map-isometry-Metric-Space-WIP =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-isometry-prop-Metric-Space-WIP A B)
      ( f)
      ( g)

  htpy-eq-map-isometry-Metric-Space-WIP :
    (f ＝ g) →
    (map-isometry-Metric-Space-WIP A B f ~ map-isometry-Metric-Space-WIP A B g)
  htpy-eq-map-isometry-Metric-Space-WIP =
    map-equiv equiv-eq-htpy-map-isometry-Metric-Space-WIP

  eq-htpy-map-isometry-Metric-Space-WIP :
    ( map-isometry-Metric-Space-WIP A B f ~
      map-isometry-Metric-Space-WIP A B g) →
    (f ＝ g)
  eq-htpy-map-isometry-Metric-Space-WIP =
    map-inv-equiv equiv-eq-htpy-map-isometry-Metric-Space-WIP
```

### An isometry preserves and reflects neighborhoods

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : isometry-Metric-Space-WIP A B)
  where

  preserves-neighborhood-map-isometry-Metric-Space-WIP :
    (d : ℚ⁺) (x y : type-Metric-Space-WIP A) →
    neighborhood-Metric-Space-WIP A d x y →
    neighborhood-Metric-Space-WIP
      ( B)
      ( d)
      ( map-isometry-Metric-Space-WIP A B f x)
      ( map-isometry-Metric-Space-WIP A B f y)
  preserves-neighborhood-map-isometry-Metric-Space-WIP d x y =
    forward-implication
      ( is-isometry-map-isometry-Metric-Space-WIP A B f d x y)

  reflects-neighborhood-map-isometry-Metric-Space-WIP :
    (d : ℚ⁺) (x y : type-Metric-Space-WIP A) →
    neighborhood-Metric-Space-WIP
      ( B)
      ( d)
      ( map-isometry-Metric-Space-WIP A B f x)
      ( map-isometry-Metric-Space-WIP A B f y) →
    neighborhood-Metric-Space-WIP A d x y
  reflects-neighborhood-map-isometry-Metric-Space-WIP d x y =
    backward-implication
      ( is-isometry-map-isometry-Metric-Space-WIP A B f d x y)
```

### Composition of isometries

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (C : Metric-Space-WIP l1c l2c)
  where

  is-isometry-comp-is-isometry-Metric-Space-WIP :
    (g : type-function-Metric-Space-WIP B C) →
    (f : type-function-Metric-Space-WIP A B) →
    is-isometry-Metric-Space-WIP B C g →
    is-isometry-Metric-Space-WIP A B f →
    is-isometry-Metric-Space-WIP A C (g ∘ f)
  is-isometry-comp-is-isometry-Metric-Space-WIP g f H K d x y =
    H d (f x) (f y) ∘iff K d x y

  comp-isometry-Metric-Space-WIP :
    isometry-Metric-Space-WIP B C →
    isometry-Metric-Space-WIP A B →
    isometry-Metric-Space-WIP A C
  comp-isometry-Metric-Space-WIP g f =
    ( map-isometry-Metric-Space-WIP B C g ∘
      map-isometry-Metric-Space-WIP A B f) ,
    ( is-isometry-comp-is-isometry-Metric-Space-WIP
      ( map-isometry-Metric-Space-WIP B C g)
      ( map-isometry-Metric-Space-WIP A B f)
      ( is-isometry-map-isometry-Metric-Space-WIP B C g)
      ( is-isometry-map-isometry-Metric-Space-WIP A B f))
```

### Unit laws for composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (f : isometry-Metric-Space-WIP A B)
  where

  left-unit-law-comp-isometry-Metric-Space-WIP :
    ( comp-isometry-Metric-Space-WIP A B B
      (isometry-id-Metric-Space-WIP B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-isometry-Metric-Space-WIP =
    eq-htpy-map-isometry-Metric-Space-WIP
      ( A)
      ( B)
      ( comp-isometry-Metric-Space-WIP
        ( A)
        ( B)
        ( B)
        (isometry-id-Metric-Space-WIP B)
        ( f))
      ( f)
      ( λ x → refl)

  right-unit-law-comp-isometry-Metric-Space-WIP :
    ( comp-isometry-Metric-Space-WIP A A B
      ( f)
      ( isometry-id-Metric-Space-WIP A)) ＝
    ( f)
  right-unit-law-comp-isometry-Metric-Space-WIP =
    eq-htpy-map-isometry-Metric-Space-WIP
      ( A)
      ( B)
      ( f)
      ( comp-isometry-Metric-Space-WIP
        ( A)
        ( A)
        ( B)
        ( f)
        ( isometry-id-Metric-Space-WIP A))
      ( λ x → refl)
```

### Associativity of composition of isometries between metric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (C : Metric-Space-WIP l1c l2c)
  (D : Metric-Space-WIP l1d l2d)
  (h : isometry-Metric-Space-WIP C D)
  (g : isometry-Metric-Space-WIP B C)
  (f : isometry-Metric-Space-WIP A B)
  where

  associative-comp-isometry-Metric-Space-WIP :
    ( comp-isometry-Metric-Space-WIP A B D
      ( comp-isometry-Metric-Space-WIP B C D h g)
      ( f)) ＝
    ( comp-isometry-Metric-Space-WIP A C D
      ( h)
      ( comp-isometry-Metric-Space-WIP A B C g f))
  associative-comp-isometry-Metric-Space-WIP =
    eq-htpy-map-isometry-Metric-Space-WIP
      ( A)
      ( D)
      ( comp-isometry-Metric-Space-WIP A B D
        ( comp-isometry-Metric-Space-WIP B C D h g)
        ( f))
      ( comp-isometry-Metric-Space-WIP A C D
        ( h)
        ( comp-isometry-Metric-Space-WIP A B C g f))
      ( λ x → refl)
```

### The inverse of an isometric equivalence is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  where

  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space-WIP :
    (f : type-function-Metric-Space-WIP A B) →
    is-isometry-Metric-Space-WIP A B f →
    (E : is-equiv f) →
    is-isometry-Metric-Space-WIP B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Metric-Space-WIP f I E d x y =
    logical-equivalence-reasoning
      ( neighborhood-Metric-Space-WIP B d x y)
      ↔ ( neighborhood-Metric-Space-WIP B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( neighborhood-Metric-Space-WIP B d x y) ↔
              ( neighborhood-Metric-Space-WIP B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( neighborhood-Metric-Space-WIP A d
          ( map-inv-is-equiv E x)
          ( map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))

module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : isometry-Metric-Space-WIP A B)
  (E : is-equiv (map-isometry-Metric-Space-WIP A B f))
  where

  isometry-inv-is-equiv-isometry-Metric-Space-WIP :
    isometry-Metric-Space-WIP B A
  isometry-inv-is-equiv-isometry-Metric-Space-WIP =
    ( map-inv-is-equiv E) ,
    ( is-isometry-map-inv-is-equiv-is-isometry-Metric-Space-WIP
      ( A)
      ( B)
      ( map-isometry-Metric-Space-WIP A B f)
      ( is-isometry-map-isometry-Metric-Space-WIP A B f)
      ( E))

  is-section-isometry-inv-is-equiv-isometry-Metric-Space-WIP :
    ( comp-isometry-Metric-Space-WIP
      B
      A
      B
      f
      isometry-inv-is-equiv-isometry-Metric-Space-WIP) ＝
    ( isometry-id-Metric-Space-WIP B)
  is-section-isometry-inv-is-equiv-isometry-Metric-Space-WIP =
    eq-htpy-map-isometry-Metric-Space-WIP
      ( B)
      ( B)
      ( comp-isometry-Metric-Space-WIP
        B
        A
        B
        f
        isometry-inv-is-equiv-isometry-Metric-Space-WIP)
      ( isometry-id-Metric-Space-WIP B)
      ( is-section-map-inv-is-equiv E)

  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space-WIP :
    ( comp-isometry-Metric-Space-WIP
      A
      B
      A
      isometry-inv-is-equiv-isometry-Metric-Space-WIP
      f) ＝
    ( isometry-id-Metric-Space-WIP A)
  is-retraction-isometry-inv-is-equiv-isometry-Metric-Space-WIP =
    eq-htpy-map-isometry-Metric-Space-WIP
      ( A)
      ( A)
      ( comp-isometry-Metric-Space-WIP
        A
        B
        A
        isometry-inv-is-equiv-isometry-Metric-Space-WIP
        f)
      ( isometry-id-Metric-Space-WIP A)
      ( is-retraction-map-inv-is-equiv E)
```

### Any isometry between metric spaces is an embedding

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : isometry-Metric-Space-WIP A B)
  where

  is-injective-map-isometry-Metric-Space-WIP :
    is-injective (map-isometry-Metric-Space-WIP A B f)
  is-injective-map-isometry-Metric-Space-WIP H =
    eq-sim-Metric-Space-WIP
      ( A)
      ( _)
      ( _)
      ( λ d →
        backward-implication
          ( is-isometry-map-isometry-Metric-Space-WIP A B f d _ _)
          ( sim-eq-Metric-Space-WIP B _ _ H d))

  is-emb-map-isometry-Metric-Space-WIP :
    is-emb (map-isometry-Metric-Space-WIP A B f)
  is-emb-map-isometry-Metric-Space-WIP =
    is-emb-is-injective
      ( is-set-type-Metric-Space-WIP B)
      ( is-injective-map-isometry-Metric-Space-WIP)
```
