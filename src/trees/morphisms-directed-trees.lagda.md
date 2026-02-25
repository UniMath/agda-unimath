# Morphisms of directed trees

```agda
module trees.morphisms-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.morphisms-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of directed trees" Agda=hom-Directed-Tree}}
of [directed trees](trees.directed-trees.md) from `S` to `T` is a
[morphism](graph-theory.morphisms-directed-graphs.md) between their underlying
[directed graphs](graph-theory.directed-graphs.md).

## Definitions

### Morphisms of directed trees

```agda
hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-Directed-Tree S T =
  hom-Directed-Graph (graph-Directed-Tree S) (graph-Directed-Tree T)

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  node-hom-Directed-Tree : node-Directed-Tree S → node-Directed-Tree T
  node-hom-Directed-Tree =
    vertex-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  edge-hom-Directed-Tree :
    {x y : node-Directed-Tree S} →
    edge-Directed-Tree S x y →
    edge-Directed-Tree T (node-hom-Directed-Tree x) (node-hom-Directed-Tree y)
  edge-hom-Directed-Tree =
    edge-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  direct-predecessor-hom-Directed-Tree :
    (x : node-Directed-Tree S) →
    Σ ( node-Directed-Tree S) (λ y → edge-Directed-Tree S y x) →
    Σ ( node-Directed-Tree T)
      ( λ y → edge-Directed-Tree T y (node-hom-Directed-Tree x))
  direct-predecessor-hom-Directed-Tree x =
    map-Σ
      ( λ y → edge-Directed-Tree T y (node-hom-Directed-Tree x))
      ( node-hom-Directed-Tree)
      ( λ y → edge-hom-Directed-Tree)

  walk-hom-Directed-Tree :
    {x y : node-Directed-Tree S} →
    walk-Directed-Tree S x y →
    walk-Directed-Tree T (node-hom-Directed-Tree x) (node-hom-Directed-Tree y)
  walk-hom-Directed-Tree =
    walk-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
```

### Identity morphisms of directed trees

```agda
id-hom-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2) → hom-Directed-Tree T T
id-hom-Directed-Tree T =
  id-hom-Directed-Graph (graph-Directed-Tree T)
```

### Composition of morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Directed-Tree l1 l2) (S : Directed-Tree l3 l4) (T : Directed-Tree l5 l6)
  (g : hom-Directed-Tree S T) (f : hom-Directed-Tree R S)
  where

  node-comp-hom-Directed-Tree :
    node-Directed-Tree R → node-Directed-Tree T
  node-comp-hom-Directed-Tree =
    vertex-comp-hom-Directed-Graph
      ( graph-Directed-Tree R)
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( g)
      ( f)

  edge-comp-hom-Directed-Tree :
    (x y : node-Directed-Tree R) (e : edge-Directed-Tree R x y) →
    edge-Directed-Tree T
      ( node-comp-hom-Directed-Tree x)
      ( node-comp-hom-Directed-Tree y)
  edge-comp-hom-Directed-Tree =
    edge-comp-hom-Directed-Graph
      ( graph-Directed-Tree R)
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( g)
      ( f)

  comp-hom-Directed-Tree :
    hom-Directed-Tree R T
  comp-hom-Directed-Tree =
    comp-hom-Directed-Graph
      ( graph-Directed-Tree R)
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( g)
      ( f)
```

### Homotopies of morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f g : hom-Directed-Tree S T)
  where

  htpy-hom-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-Directed-Tree =
    htpy-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
      ( g)

  node-htpy-hom-Directed-Tree :
    htpy-hom-Directed-Tree →
    node-hom-Directed-Tree S T f ~ node-hom-Directed-Tree S T g
  node-htpy-hom-Directed-Tree =
    vertex-htpy-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
      ( g)

  edge-htpy-hom-Directed-Tree :
    ( α : htpy-hom-Directed-Tree) →
    ( x y : node-Directed-Tree S) (e : edge-Directed-Tree S x y) →
    binary-tr
      ( edge-Directed-Tree T)
      ( node-htpy-hom-Directed-Tree α x)
      ( node-htpy-hom-Directed-Tree α y)
      ( edge-hom-Directed-Tree S T f e) ＝
    edge-hom-Directed-Tree S T g e
  edge-htpy-hom-Directed-Tree =
    edge-htpy-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
      ( g)

  direct-predecessor-htpy-hom-Directed-Tree :
    ( α : htpy-hom-Directed-Tree) →
    ( x : node-Directed-Tree S) →
    ( ( tot
        ( λ y →
          tr
            ( edge-Directed-Tree T y)
            ( node-htpy-hom-Directed-Tree α x))) ∘
      ( direct-predecessor-hom-Directed-Tree S T f x)) ~
    ( direct-predecessor-hom-Directed-Tree S T g x)
  direct-predecessor-htpy-hom-Directed-Tree α x (y , e) =
    eq-pair-Σ
      ( node-htpy-hom-Directed-Tree α y)
      ( ( compute-binary-tr
          ( edge-Directed-Tree T)
          ( node-htpy-hom-Directed-Tree α y)
          ( node-htpy-hom-Directed-Tree α x)
          ( edge-hom-Directed-Tree S T f e)) ∙
        ( edge-htpy-hom-Directed-Tree α y x e))
```

### The reflexivity homotopy of morphisms of directed trees

```agda
refl-htpy-hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  (f : hom-Directed-Tree S T) → htpy-hom-Directed-Tree S T f f
refl-htpy-hom-Directed-Tree S T f =
  refl-htpy-hom-Directed-Graph
    ( graph-Directed-Tree S)
    ( graph-Directed-Tree T)
    ( f)
```

## Properties

### Homotopies characterize identifications of morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  is-torsorial-htpy-hom-Directed-Tree :
    is-torsorial (htpy-hom-Directed-Tree S T f)
  is-torsorial-htpy-hom-Directed-Tree =
    is-torsorial-htpy-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  htpy-eq-hom-Directed-Tree :
    (g : hom-Directed-Tree S T) → f ＝ g → htpy-hom-Directed-Tree S T f g
  htpy-eq-hom-Directed-Tree =
    htpy-eq-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  is-equiv-htpy-eq-hom-Directed-Tree :
    (g : hom-Directed-Tree S T) → is-equiv (htpy-eq-hom-Directed-Tree g)
  is-equiv-htpy-eq-hom-Directed-Tree =
    is-equiv-htpy-eq-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  extensionality-hom-Directed-Tree :
    (g : hom-Directed-Tree S T) → (f ＝ g) ≃ htpy-hom-Directed-Tree S T f g
  extensionality-hom-Directed-Tree =
    extensionality-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  eq-htpy-hom-Directed-Tree :
    (g : hom-Directed-Tree S T) → htpy-hom-Directed-Tree S T f g → f ＝ g
  eq-htpy-hom-Directed-Tree =
    eq-htpy-hom-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
```

### If `f x` is the root of `T`, then `x` is the root of `S`

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  is-root-is-root-node-hom-Directed-Tree :
    (x : node-Directed-Tree S) →
    is-root-Directed-Tree T (node-hom-Directed-Tree S T f x) →
    is-root-Directed-Tree S x
  is-root-is-root-node-hom-Directed-Tree x H =
    map-right-unit-law-coproduct-is-empty
      ( is-root-Directed-Tree S x)
      ( Σ (node-Directed-Tree S) (edge-Directed-Tree S x))
      ( λ (y , e) →
        no-direct-successor-root-Directed-Tree T
          ( tr
            ( λ u → Σ (node-Directed-Tree T) (edge-Directed-Tree T u))
            ( inv H)
            ( node-hom-Directed-Tree S T f y ,
              edge-hom-Directed-Tree S T f e)))
      ( center (unique-direct-successor-Directed-Tree S x))

  is-not-root-node-hom-is-not-root-Directed-Tree :
    (x : node-Directed-Tree S) →
    ¬ (is-root-Directed-Tree S x) →
    ¬ (is-root-Directed-Tree T (node-hom-Directed-Tree S T f x))
  is-not-root-node-hom-is-not-root-Directed-Tree x =
    map-neg (is-root-is-root-node-hom-Directed-Tree x)
```

## See also

- Root-preserving morphisms of directed trees are introduced in
  [`rooted-morphisms-directed-trees`](trees.rooted-morphisms-directed-trees.md)
