# Short functions between pseudometric spaces

```agda
module metric-spaces.short-functions-pseudometric-spaces where
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

open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.poset-of-rational-neighborhood-relations
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-pseudometric-spaces.md) `f` between two
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) `A` and `B` is
{{#concept "short" Disambiguation="function between pseudometric spaces" Agda=is-short-function-Pseudometric-Space WD="metric map" WDID=Q2713824}}
if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is [finer](metric-spaces.poset-of-rational-neighborhood-relations.md)
than the [preimage](metric-spaces.preimages-rational-neighborhood-relations.md)
by `f` of the rational neighborhood relation on `B`. I.e., upper bounds on the
distance between two points in `A` are upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a short function between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : type-function-Pseudometric-Space A B)
  where

  is-short-function-prop-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-function-prop-Pseudometric-Space =
    leq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Pseudometric-Space B))

  is-short-function-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-function-Pseudometric-Space =
    type-Prop is-short-function-prop-Pseudometric-Space

  is-prop-is-short-function-Pseudometric-Space :
    is-prop is-short-function-Pseudometric-Space
  is-prop-is-short-function-Pseudometric-Space =
    is-prop-type-Prop is-short-function-prop-Pseudometric-Space
```

### The set of short functions between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  short-function-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-function-Pseudometric-Space =
    type-subtype (is-short-function-prop-Pseudometric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-function-Pseudometric-Space A B)
  where

  map-short-function-Pseudometric-Space : type-function-Pseudometric-Space A B
  map-short-function-Pseudometric-Space = pr1 f

  is-short-map-short-function-Pseudometric-Space :
    is-short-function-Pseudometric-Space A B
      map-short-function-Pseudometric-Space
  is-short-map-short-function-Pseudometric-Space = pr2 f
```

## Properties

### The identity function on a pseudometric space is short

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-short-id-Pseudometric-Space :
    is-short-function-Pseudometric-Space A A (id-Pseudometric-Space A)
  is-short-id-Pseudometric-Space d x y H = H

  short-id-Pseudometric-Space : short-function-Pseudometric-Space A A
  short-id-Pseudometric-Space =
    id-Pseudometric-Space A , is-short-id-Pseudometric-Space
```

### Equality of short functions between pseudometric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f g : short-function-Pseudometric-Space A B)
  where

  equiv-eq-htpy-map-short-function-Pseudometric-Space :
    ( f ＝ g) ≃
    ( map-short-function-Pseudometric-Space A B f ~
      map-short-function-Pseudometric-Space A B g)
  equiv-eq-htpy-map-short-function-Pseudometric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-function-prop-Pseudometric-Space A B) f g

  eq-htpy-map-short-function-Pseudometric-Space :
    ( map-short-function-Pseudometric-Space A B f ~
      map-short-function-Pseudometric-Space A B g) →
    ( f ＝ g)
  eq-htpy-map-short-function-Pseudometric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-function-Pseudometric-Space
```

### Composition of short functions between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  where

  is-short-comp-is-short-function-Pseudometric-Space :
    (g : type-function-Pseudometric-Space B C) →
    (f : type-function-Pseudometric-Space A B) →
    is-short-function-Pseudometric-Space B C g →
    is-short-function-Pseudometric-Space A B f →
    is-short-function-Pseudometric-Space A C (g ∘ f)
  is-short-comp-is-short-function-Pseudometric-Space g f H K d x y =
    H d (f x) (f y) ∘ K d x y

  comp-short-function-Pseudometric-Space :
    short-function-Pseudometric-Space B C →
    short-function-Pseudometric-Space A B →
    short-function-Pseudometric-Space A C
  comp-short-function-Pseudometric-Space g f =
    ( map-short-function-Pseudometric-Space B C g ∘
      map-short-function-Pseudometric-Space A B f) ,
    ( is-short-comp-is-short-function-Pseudometric-Space
      ( map-short-function-Pseudometric-Space B C g)
      ( map-short-function-Pseudometric-Space A B f)
      ( is-short-map-short-function-Pseudometric-Space B C g)
      ( is-short-map-short-function-Pseudometric-Space A B f))
```

### Unit laws for composition of short maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (f : short-function-Pseudometric-Space A B)
  where

  left-unit-law-comp-short-function-Pseudometric-Space :
    ( comp-short-function-Pseudometric-Space A B B
      ( short-id-Pseudometric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-short-function-Pseudometric-Space =
    eq-htpy-map-short-function-Pseudometric-Space
      ( A)
      ( B)
      ( comp-short-function-Pseudometric-Space
        ( A)
        ( B)
        ( B)
        ( short-id-Pseudometric-Space B)
        ( f))
      ( f)
      ( λ x → refl)

  right-unit-law-comp-short-function-Pseudometric-Space :
    ( comp-short-function-Pseudometric-Space A A B
      ( f)
      ( short-id-Pseudometric-Space A)) ＝
    ( f)
  right-unit-law-comp-short-function-Pseudometric-Space =
    eq-htpy-map-short-function-Pseudometric-Space
      ( A)
      ( B)
      ( f)
      ( comp-short-function-Pseudometric-Space
        ( A)
        ( A)
        ( B)
        ( f)
        ( short-id-Pseudometric-Space A))
      ( λ x → refl)
```

### Associativity of composition of short maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  (D : Pseudometric-Space l1d l2d)
  (h : short-function-Pseudometric-Space C D)
  (g : short-function-Pseudometric-Space B C)
  (f : short-function-Pseudometric-Space A B)
  where

  associative-comp-short-function-Pseudometric-Space :
    ( comp-short-function-Pseudometric-Space A B D
      ( comp-short-function-Pseudometric-Space B C D h g)
        ( f)) ＝
    ( comp-short-function-Pseudometric-Space A C D
      ( h)
      ( comp-short-function-Pseudometric-Space A B C g f))
  associative-comp-short-function-Pseudometric-Space =
    eq-htpy-map-short-function-Pseudometric-Space
      ( A)
      ( D)
      ( comp-short-function-Pseudometric-Space A B D
        ( comp-short-function-Pseudometric-Space B C D h g)
        ( f))
      ( comp-short-function-Pseudometric-Space A C D
        ( h)
        ( comp-short-function-Pseudometric-Space A B C g f))
      ( λ x → refl)
```

### Constant functions between pseudometric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (b : type-Pseudometric-Space B)
  where

  is-short-constant-function-Pseudometric-Space :
    is-short-function-Pseudometric-Space A B (λ _ → b)
  is-short-constant-function-Pseudometric-Space ε x y H =
    refl-neighborhood-Pseudometric-Space B ε b

  short-constant-function-Pseudometric-Space :
    short-function-Pseudometric-Space A B
  pr1 short-constant-function-Pseudometric-Space _ = b
  pr2 short-constant-function-Pseudometric-Space =
    is-short-constant-function-Pseudometric-Space
```

### Any isometry between pseudometric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : type-function-Pseudometric-Space A B)
  where

  is-short-is-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space A B f →
    is-short-function-Pseudometric-Space A B f
  is-short-is-isometry-Pseudometric-Space I =
    preserves-neighborhood-map-isometry-Pseudometric-Space A B (f , I)
```

### The embedding of isometries of pseudometric spaces into short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  short-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B → short-function-Pseudometric-Space A B
  short-isometry-Pseudometric-Space f =
    map-isometry-Pseudometric-Space A B f ,
    is-short-is-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( map-isometry-Pseudometric-Space A B f)
      ( is-isometry-map-isometry-Pseudometric-Space A B f)

  is-emb-short-isometry-Pseudometric-Space :
    is-emb short-isometry-Pseudometric-Space
  is-emb-short-isometry-Pseudometric-Space =
    is-emb-right-factor
      ( map-short-function-Pseudometric-Space A B)
      ( short-isometry-Pseudometric-Space)
      ( is-emb-inclusion-subtype
        ( is-short-function-prop-Pseudometric-Space A B))
      ( is-emb-htpy
        ( λ f → refl)
        ( is-emb-inclusion-subtype (is-isometry-prop-Pseudometric-Space A B)))

  emb-short-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B ↪ short-function-Pseudometric-Space A B
  emb-short-isometry-Pseudometric-Space =
    short-isometry-Pseudometric-Space ,
    is-emb-short-isometry-Pseudometric-Space
```
