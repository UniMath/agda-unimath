# Equivalences of directed trees

```agda
module trees.equivalences-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.equivalences-directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.directed-trees
open import trees.morphisms-directed-trees
open import trees.rooted-morphisms-directed-trees
```

</details>

## Idea

{{#concept "Equivalences" Disambiguation="of directed trees" Agda=equiv-Directed-Tree}}
of [directed trees](trees.directed-trees.md) are
[morphisms](trees.morphisms-directed-trees.md) of directed trees of which the
actions on nodes and on edges are both
[equivalences](foundation-core.equivalences.md). In other words, equivalences of
directed trees are just equivalences between their underlying
[directed graphs](graph-theory.directed-graphs.md).

## Definitions

### The condition of being an equivalence of directed trees

```agda
is-equiv-hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  hom-Directed-Tree S T → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-equiv-hom-Directed-Tree S T =
  is-equiv-hom-Directed-Graph (graph-Directed-Tree S) (graph-Directed-Tree T)
```

### Equivalences of directed trees

```agda
equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Tree S T =
  equiv-Directed-Graph (graph-Directed-Tree S) (graph-Directed-Tree T)

equiv-is-equiv-hom-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  (f : hom-Directed-Tree S T) → is-equiv-hom-Directed-Tree S T f →
  equiv-Directed-Tree S T
equiv-is-equiv-hom-Directed-Tree S T =
  equiv-is-equiv-hom-Directed-Graph
    ( graph-Directed-Tree S)
    ( graph-Directed-Tree T)

compute-equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4) →
  equiv-Directed-Tree S T ≃
  Σ (hom-Directed-Tree S T) (is-equiv-hom-Directed-Tree S T)
compute-equiv-Directed-Tree S T =
  compute-equiv-Directed-Graph
    ( graph-Directed-Tree S)
    ( graph-Directed-Tree T)

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  node-equiv-equiv-Directed-Tree :
    node-Directed-Tree S ≃ node-Directed-Tree T
  node-equiv-equiv-Directed-Tree =
    vertex-equiv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  node-equiv-Directed-Tree :
    node-Directed-Tree S → node-Directed-Tree T
  node-equiv-Directed-Tree =
    vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-node-equiv-equiv-Directed-Tree : is-equiv node-equiv-Directed-Tree
  is-node-equiv-equiv-Directed-Tree =
    is-vertex-equiv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  inv-node-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  inv-node-equiv-Directed-Tree =
    inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-section-inv-node-equiv-Directed-Tree :
    ( node-equiv-Directed-Tree ∘ inv-node-equiv-Directed-Tree) ~ id
  is-section-inv-node-equiv-Directed-Tree =
    is-section-inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-retraction-inv-node-equiv-Directed-Tree :
    ( inv-node-equiv-Directed-Tree ∘ node-equiv-Directed-Tree) ~ id
  is-retraction-inv-node-equiv-Directed-Tree =
    is-retraction-inv-vertex-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  edge-equiv-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) →
    edge-Directed-Tree S x y ≃
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  edge-equiv-equiv-Directed-Tree =
    edge-equiv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  edge-equiv-Directed-Tree :
    {x y : node-Directed-Tree S} →
    edge-Directed-Tree S x y →
    edge-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  edge-equiv-Directed-Tree =
    edge-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-edge-equiv-equiv-Directed-Tree :
    (x y : node-Directed-Tree S) → is-equiv (edge-equiv-Directed-Tree {x} {y})
  is-edge-equiv-equiv-Directed-Tree =
    is-edge-equiv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  hom-equiv-Directed-Tree : hom-Directed-Tree S T
  hom-equiv-Directed-Tree =
    hom-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-equiv-equiv-Directed-Tree :
    is-equiv-hom-Directed-Tree S T hom-equiv-Directed-Tree
  is-equiv-equiv-Directed-Tree =
    is-equiv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  equiv-direct-predecessor-equiv-Directed-Tree :
    (x : node-Directed-Tree S) →
    ( Σ (node-Directed-Tree S) (λ y → edge-Directed-Tree S y x)) ≃
    ( Σ ( node-Directed-Tree T)
        ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x)))
  equiv-direct-predecessor-equiv-Directed-Tree x =
    equiv-Σ
      ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x))
      ( node-equiv-equiv-Directed-Tree)
      ( λ y → edge-equiv-equiv-Directed-Tree y x)

  direct-predecessor-equiv-Directed-Tree :
    (x : node-Directed-Tree S) →
    Σ (node-Directed-Tree S) (λ y → edge-Directed-Tree S y x) →
    Σ ( node-Directed-Tree T)
      ( λ y → edge-Directed-Tree T y (node-equiv-Directed-Tree x))
  direct-predecessor-equiv-Directed-Tree x =
    map-equiv (equiv-direct-predecessor-equiv-Directed-Tree x)

  equiv-walk-equiv-Directed-Tree :
    {x y : node-Directed-Tree S} →
    walk-Directed-Tree S x y ≃
    walk-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  equiv-walk-equiv-Directed-Tree =
    equiv-walk-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  walk-equiv-Directed-Tree :
    {x y : node-Directed-Tree S} →
    walk-Directed-Tree S x y →
    walk-Directed-Tree T
      ( node-equiv-Directed-Tree x)
      ( node-equiv-Directed-Tree y)
  walk-equiv-Directed-Tree =
    walk-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)
```

### Identity equivalences of directed trees

```agda
id-equiv-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2) → equiv-Directed-Tree T T
id-equiv-Directed-Tree T = id-equiv-Directed-Graph (graph-Directed-Tree T)
```

### Composition of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Directed-Tree l1 l2) (S : Directed-Tree l3 l4) (T : Directed-Tree l5 l6)
  (g : equiv-Directed-Tree S T) (f : equiv-Directed-Tree R S)
  where

  comp-equiv-Directed-Tree : equiv-Directed-Tree R T
  comp-equiv-Directed-Tree =
    comp-equiv-Directed-Graph
      ( graph-Directed-Tree R)
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( g)
      ( f)

  node-equiv-comp-equiv-Directed-Tree :
    node-Directed-Tree R ≃ node-Directed-Tree T
  node-equiv-comp-equiv-Directed-Tree =
    node-equiv-equiv-Directed-Tree R T comp-equiv-Directed-Tree

  node-comp-equiv-Directed-Tree :
    node-Directed-Tree R → node-Directed-Tree T
  node-comp-equiv-Directed-Tree =
    node-equiv-Directed-Tree R T comp-equiv-Directed-Tree

  edge-equiv-comp-equiv-Directed-Tree :
    (x y : node-Directed-Tree R) →
    edge-Directed-Tree R x y ≃
    edge-Directed-Tree T
      ( node-comp-equiv-Directed-Tree x)
      ( node-comp-equiv-Directed-Tree y)
  edge-equiv-comp-equiv-Directed-Tree =
    edge-equiv-equiv-Directed-Tree R T comp-equiv-Directed-Tree

  edge-comp-equiv-Directed-Tree :
    {x y : node-Directed-Tree R} →
    edge-Directed-Tree R x y →
    edge-Directed-Tree T
      ( node-comp-equiv-Directed-Tree x)
      ( node-comp-equiv-Directed-Tree y)
  edge-comp-equiv-Directed-Tree =
    edge-equiv-Directed-Tree R T comp-equiv-Directed-Tree
```

### Homotopies of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f g : equiv-Directed-Tree S T)
  where

  htpy-equiv-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-equiv-Directed-Tree =
    htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)

  node-htpy-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree →
    node-equiv-Directed-Tree S T f ~ node-equiv-Directed-Tree S T g
  node-htpy-equiv-Directed-Tree =
    node-htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)

  edge-htpy-equiv-Directed-Tree :
    (α : htpy-equiv-Directed-Tree) (x y : node-Directed-Tree S)
    (e : edge-Directed-Tree S x y) →
    binary-tr
      ( edge-Directed-Tree T)
      ( node-htpy-equiv-Directed-Tree α x)
      ( node-htpy-equiv-Directed-Tree α y)
      ( edge-equiv-Directed-Tree S T f e) ＝
    edge-equiv-Directed-Tree S T g e
  edge-htpy-equiv-Directed-Tree =
    edge-htpy-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T f)
      ( hom-equiv-Directed-Tree S T g)
```

### The reflexivity homotopy of equivalences of directed trees

```agda
refl-htpy-equiv-Directed-Tree :
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T f f
refl-htpy-equiv-Directed-Tree S T f =
  refl-htpy-hom-Directed-Tree S T (hom-equiv-Directed-Tree S T f)
```

## Properties

### Homotopies characterize the identity type of equivalences of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  is-torsorial-htpy-equiv-Directed-Tree :
    is-torsorial (htpy-equiv-Directed-Tree S T e)
  is-torsorial-htpy-equiv-Directed-Tree =
    is-torsorial-htpy-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) → htpy-equiv-Directed-Tree S T e f
  htpy-eq-equiv-Directed-Tree =
    htpy-eq-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  is-equiv-htpy-eq-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → is-equiv (htpy-eq-equiv-Directed-Tree f)
  is-equiv-htpy-eq-equiv-Directed-Tree =
    is-equiv-htpy-eq-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  extensionality-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → (e ＝ f) ≃ htpy-equiv-Directed-Tree S T e f
  extensionality-equiv-Directed-Tree =
    extensionality-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)

  eq-htpy-equiv-Directed-Tree :
    (f : equiv-Directed-Tree S T) → htpy-equiv-Directed-Tree S T e f → e ＝ f
  eq-htpy-equiv-Directed-Tree =
    eq-htpy-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( e)
```

### Equivalences of directed trees preserve the root

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  preserves-root-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) →
    preserves-root-hom-Directed-Tree S T f
  preserves-root-is-equiv-node-hom-Directed-Tree H =
    ( inv (is-section-map-inv-is-equiv H (root-Directed-Tree T))) ∙
    ( inv
      ( ap
        ( node-hom-Directed-Tree S T f)
        ( is-root-is-root-node-hom-Directed-Tree S T f
          ( map-inv-is-equiv H (root-Directed-Tree T))
          ( inv (is-section-map-inv-is-equiv H (root-Directed-Tree T))))))

module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (e : equiv-Directed-Tree S T)
  where

  preserves-root-equiv-Directed-Tree :
    preserves-root-hom-Directed-Tree S T (hom-equiv-Directed-Tree S T e)
  preserves-root-equiv-Directed-Tree =
    preserves-root-is-equiv-node-hom-Directed-Tree S T
      ( hom-equiv-Directed-Tree S T e)
      ( is-node-equiv-equiv-Directed-Tree S T e)

  rooted-hom-equiv-Directed-Tree :
    rooted-hom-Directed-Tree S T
  pr1 rooted-hom-equiv-Directed-Tree = hom-equiv-Directed-Tree S T e
  pr2 rooted-hom-equiv-Directed-Tree = preserves-root-equiv-Directed-Tree
```

### Equivalences characterize identifications of trees

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  extensionality-Directed-Tree :
    (S : Directed-Tree l1 l2) → (T ＝ S) ≃ equiv-Directed-Tree T S
  extensionality-Directed-Tree =
    extensionality-type-subtype
      ( is-tree-directed-graph-Prop)
      ( is-tree-Directed-Tree T)
      ( id-equiv-Directed-Graph (graph-Directed-Tree T))
      ( extensionality-Directed-Graph (graph-Directed-Tree T))

  equiv-eq-Directed-Tree :
    (S : Directed-Tree l1 l2) → (T ＝ S) → equiv-Directed-Tree T S
  equiv-eq-Directed-Tree S = map-equiv (extensionality-Directed-Tree S)

  eq-equiv-Directed-Tree :
    (S : Directed-Tree l1 l2) → equiv-Directed-Tree T S → (T ＝ S)
  eq-equiv-Directed-Tree S = map-inv-equiv (extensionality-Directed-Tree S)

  is-torsorial-equiv-Directed-Tree :
    is-torsorial (equiv-Directed-Tree T)
  is-torsorial-equiv-Directed-Tree =
    is-contr-equiv'
      ( Σ (Directed-Tree l1 l2) (λ S → T ＝ S))
      ( equiv-tot extensionality-Directed-Tree)
      ( is-torsorial-Id T)
```

### A morphism of directed trees is an equivalence if it is an equivalence on the nodes

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : hom-Directed-Tree S T)
  where

  is-equiv-total-edge-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) → (x : node-Directed-Tree S) →
    is-equiv
      ( map-Σ
        ( edge-Directed-Tree T (node-hom-Directed-Tree S T f x))
        ( node-hom-Directed-Tree S T f)
        ( λ y → edge-hom-Directed-Tree S T f {x} {y}))
  is-equiv-total-edge-is-equiv-node-hom-Directed-Tree H x with
    is-isolated-root-Directed-Tree S x
  ... | inl refl =
    is-equiv-is-empty _
      ( λ u →
        no-direct-successor-root-Directed-Tree T
          ( tr
            ( λ v → Σ (node-Directed-Tree T) (edge-Directed-Tree T v))
            ( inv (preserves-root-is-equiv-node-hom-Directed-Tree S T f H))
            ( u)))
  ... | inr p =
    is-equiv-is-contr _
      ( unique-direct-successor-is-proper-node-Directed-Tree S x p)
      ( unique-direct-successor-is-proper-node-Directed-Tree T
        ( node-hom-Directed-Tree S T f x)
        ( is-not-root-node-hom-is-not-root-Directed-Tree S T f x p))

  is-equiv-is-equiv-node-hom-Directed-Tree :
    is-equiv (node-hom-Directed-Tree S T f) →
    is-equiv-hom-Directed-Tree S T f
  pr1 (is-equiv-is-equiv-node-hom-Directed-Tree H) = H
  pr2 (is-equiv-is-equiv-node-hom-Directed-Tree H) x =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( edge-Directed-Tree T (node-hom-Directed-Tree S T f x))
      ( node-hom-Directed-Tree S T f)
      ( λ y → edge-hom-Directed-Tree S T f {x} {y})
      ( H)
      ( is-equiv-total-edge-is-equiv-node-hom-Directed-Tree H x)
```

### The inverse of an equivalence of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : equiv-Directed-Tree S T)
  where

  inv-equiv-Directed-Tree : equiv-Directed-Tree T S
  inv-equiv-Directed-Tree =
    inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  hom-inv-equiv-Directed-Tree : hom-Directed-Tree T S
  hom-inv-equiv-Directed-Tree =
    hom-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  node-equiv-inv-equiv-Directed-Tree :
    node-Directed-Tree T ≃ node-Directed-Tree S
  node-equiv-inv-equiv-Directed-Tree =
    vertex-equiv-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  node-inv-equiv-Directed-Tree :
    node-Directed-Tree T → node-Directed-Tree S
  node-inv-equiv-Directed-Tree =
    vertex-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  edge-inv-equiv-Directed-Tree :
    {x y : node-Directed-Tree T} →
    edge-Directed-Tree T x y →
    edge-Directed-Tree S
      ( node-inv-equiv-Directed-Tree x)
      ( node-inv-equiv-Directed-Tree y)
  edge-inv-equiv-Directed-Tree =
    edge-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  edge-equiv-inv-equiv-Directed-Tree :
    (x y : node-Directed-Tree T) →
    edge-Directed-Tree T x y ≃
    edge-Directed-Tree S
      ( node-inv-equiv-Directed-Tree x)
      ( node-inv-equiv-Directed-Tree y)
  edge-equiv-inv-equiv-Directed-Tree =
    edge-equiv-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  is-section-inv-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree T T
      ( comp-equiv-Directed-Tree T S T f inv-equiv-Directed-Tree)
      ( id-equiv-Directed-Tree T)
  is-section-inv-equiv-Directed-Tree =
    is-section-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)

  is-retraction-inv-equiv-Directed-Tree :
    htpy-equiv-Directed-Tree S S
      ( comp-equiv-Directed-Tree S T S inv-equiv-Directed-Tree f)
      ( id-equiv-Directed-Tree S)
  is-retraction-inv-equiv-Directed-Tree =
    is-retraction-inv-equiv-Directed-Graph
      ( graph-Directed-Tree S)
      ( graph-Directed-Tree T)
      ( f)
```
