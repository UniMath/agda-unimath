# The directed circle

```agda
module simplicial-type-theory.directed-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import reflection.erasing-equality

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.directed-relation-on-directed-interval-type
open import simplicial-type-theory.free-directed-loops
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-edges
open import simplicial-type-theory.universal-property-directed-circle

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

The {{#concept "directed circle"}} is the type consisting of a point `*` and a
nontrivial [directed edge](simplicial-type-theory.simplicial-edges.md) `* →₂ *`.
The directed circle classifies
[free directed loops](simplicial-type-theory.free-directed-loops.md), meaning
that maps `directed-circle → X` are in correspondence with free directed loops
of `X`.

The directed circle also satisfies the
[universal property of the coequalizer](synthetic-homotopy-theory.universal-property-coequalizers.md)
of the diagram

```text
       0₂
    ------->
  1          𝟚.
    ------->
       1₂
```

## Postulates

### The standard directed circle type

```agda
postulate
  directed-circle : UU lzero

postulate
  arrow-directed-circle : simplicial-arrow directed-circle

base-directed-circle : directed-circle
base-directed-circle = arrow-directed-circle 0₂

compute-target-arrow-directed-circle :
  arrow-directed-circle 1₂ ＝ base-directed-circle
compute-target-arrow-directed-circle =
  primEraseEquality compute-target-arrow-directed-circle'
  where postulate
  compute-target-arrow-directed-circle' :
    arrow-directed-circle 1₂ ＝ base-directed-circle

compute-source-arrow-directed-circle :
  arrow-directed-circle 0₂ ＝ base-directed-circle
compute-source-arrow-directed-circle = refl

eq-source-target-arrow-directed-circle :
  arrow-directed-circle 1₂ ＝ arrow-directed-circle 0₂
eq-source-target-arrow-directed-circle =
  compute-target-arrow-directed-circle

eq-target-source-arrow-directed-circle :
  arrow-directed-circle 0₂ ＝ arrow-directed-circle 1₂
eq-target-source-arrow-directed-circle =
  inv compute-target-arrow-directed-circle

free-loop-directed-circle : free-directed-loop directed-circle
free-loop-directed-circle =
  ( arrow-directed-circle , eq-source-target-arrow-directed-circle)

loop-directed-circle : base-directed-circle →₂ base-directed-circle
loop-directed-circle =
  ( arrow-directed-circle ,
    compute-source-arrow-directed-circle ,
    compute-target-arrow-directed-circle)
```

### The induction principle of the standard directed circle

```agda
module _
  {l : Level} (P : directed-circle → UU l)
  where

  postulate
    ind-directed-circle :
      free-dependent-directed-loop free-loop-directed-circle P →
      (x : directed-circle) → P x

  compute-arrow-ind-directed-circle :
    (α : free-dependent-directed-loop free-loop-directed-circle P) (t : 𝟚) →
    ind-directed-circle α (arrow-directed-circle t) ＝
    arrow-free-dependent-directed-loop free-loop-directed-circle α t
  compute-arrow-ind-directed-circle α t =
    primEraseEquality compute-arrow-ind-directed-circle'
    where postulate
      compute-arrow-ind-directed-circle' :
        ind-directed-circle α (arrow-directed-circle t) ＝
        arrow-free-dependent-directed-loop free-loop-directed-circle α t

  postulate
    coherence-ind-directed-circle :
      (α : free-dependent-directed-loop free-loop-directed-circle P) →
      coherence-htpy-free-dependent-directed-loop
        ( free-loop-directed-circle)
        ( P)
        ( ev-free-directed-loop-Π free-loop-directed-circle P
          ( ind-directed-circle α))
        ( α)
        ( compute-arrow-ind-directed-circle α)

  compute-ind-directed-circle :
    is-section
      ( ev-free-directed-loop-Π free-loop-directed-circle P)
      ( ind-directed-circle)
  compute-ind-directed-circle α =
    eq-htpy-free-dependent-directed-loop free-loop-directed-circle P
      ( ev-free-directed-loop-Π free-loop-directed-circle P
        ( ind-directed-circle α))
      ( α)
      ( compute-arrow-ind-directed-circle α , coherence-ind-directed-circle α)

induction-principle-directed-circle' :
  induction-principle-directed-circle free-loop-directed-circle
induction-principle-directed-circle' P =
  ( ind-directed-circle P , compute-ind-directed-circle P)
```

## Definitions

### The dependent universal property of the directed circle

```agda
dup-directed-circle :
  dependent-universal-property-directed-circle free-loop-directed-circle
dup-directed-circle =
  dependent-universal-property-induction-principle-directed-circle
    ( free-loop-directed-circle)
    ( induction-principle-directed-circle')
```

### The universal property of the directed circle

```agda
up-directed-circle :
  universal-property-directed-circle free-loop-directed-circle
up-directed-circle =
  universal-property-induction-principle-directed-circle
    ( free-loop-directed-circle)
    ( induction-principle-directed-circle')
```

### The recursion principle of the directed circle

```agda
module _
  {l : Level} {X : UU l}
  where

  rec-directed-circle : free-directed-loop X → directed-circle → X
  rec-directed-circle α =
    ind-directed-circle
      ( λ _ → X)
      ( map-compute-free-dependent-directed-loop-constant-type-family
        ( free-loop-directed-circle)
        ( X)
        ( α))

  compute-arrow-rec-directed-circle :
    (α : free-directed-loop X) →
    rec-directed-circle α ∘ arrow-directed-circle ~
    arrow-free-directed-loop α
  compute-arrow-rec-directed-circle α =
    compute-arrow-ind-directed-circle
      ( λ _ → X)
      ( map-compute-free-dependent-directed-loop-constant-type-family
        ( free-loop-directed-circle)
        ( X)
        ( α))
```

## Properties

### The directed circle as a coequalizer

The directed circle satisfies the universal property of the coequalizer of the
diagram

```text
       0₂
    ------->
  1          𝟚.
    ------->
       1₂
```

This remains to be formalized.

### The canonical comparison map to the homotopic circle

```agda
map-directed-circle-circle : directed-circle → 𝕊¹
map-directed-circle-circle =
  rec-directed-circle (free-directed-loop-free-loop free-loop-𝕊¹)

compute-map-directed-circle-circle-id-arrow :
  (x : directed-circle) →
  map-directed-circle-circle ∘ id-simplicial-arrow x ~
  id-simplicial-arrow (map-directed-circle-circle x)
compute-map-directed-circle-circle-id-arrow x = refl-htpy
```

### The loop of the directed circle is nontrivial

This remains to be formalized.
