# Rooted morphisms of directed trees

```agda
module trees.rooted-morphisms-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.pointed-maps

open import trees.directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

A **rooted morphism** of directed trees from `S` to `T` is a morphism of
directed trees that maps the root of `S` to the root of `T`

## Definition

### Rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  where

  preserves-root-hom-directed-tree-Prop : hom-Directed-Tree S T → Prop l3
  preserves-root-hom-directed-tree-Prop f =
    is-root-directed-tree-Prop T
      ( node-hom-Directed-Tree S T f (root-Directed-Tree S))

  preserves-root-hom-Directed-Tree :
    hom-Directed-Tree S T → UU l3
  preserves-root-hom-Directed-Tree f =
    type-Prop (preserves-root-hom-directed-tree-Prop f)

  is-prop-preserves-root-hom-Directed-Tree :
    (f : hom-Directed-Tree S T) → is-prop (preserves-root-hom-Directed-Tree f)
  is-prop-preserves-root-hom-Directed-Tree f =
    is-prop-type-Prop (preserves-root-hom-directed-tree-Prop f)

  rooted-hom-Directed-Tree : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  rooted-hom-Directed-Tree =
    Σ (hom-Directed-Tree S T) preserves-root-hom-Directed-Tree

  module _
    (f : rooted-hom-Directed-Tree)
    where

    hom-rooted-hom-Directed-Tree : hom-Directed-Tree S T
    hom-rooted-hom-Directed-Tree = pr1 f

    node-rooted-hom-Directed-Tree :
      node-Directed-Tree S → node-Directed-Tree T
    node-rooted-hom-Directed-Tree =
      node-hom-Directed-Tree S T hom-rooted-hom-Directed-Tree

    edge-rooted-hom-Directed-Tree :
      {x y : node-Directed-Tree S} →
      edge-Directed-Tree S x y →
      edge-Directed-Tree T
        ( node-rooted-hom-Directed-Tree x)
        ( node-rooted-hom-Directed-Tree y)
    edge-rooted-hom-Directed-Tree =
      edge-hom-Directed-Tree S T hom-rooted-hom-Directed-Tree

    preserves-root-rooted-hom-Directed-Tree :
      preserves-root-hom-Directed-Tree hom-rooted-hom-Directed-Tree
    preserves-root-rooted-hom-Directed-Tree = pr2 f
```

### The identity rooted morphism of directed trees

```agda
id-rooted-hom-Directed-Tree :
  {l1 l2 : Level} (T : Directed-Tree l1 l2) → rooted-hom-Directed-Tree T T
pr1 (id-rooted-hom-Directed-Tree T) = id-hom-Directed-Tree T
pr2 (id-rooted-hom-Directed-Tree T) = refl
```

### Composition of rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (R : Directed-Tree l1 l2) (S : Directed-Tree l3 l4) (T : Directed-Tree l5 l6)
  (g : rooted-hom-Directed-Tree S T)
  (f : rooted-hom-Directed-Tree R S)
  where

  hom-comp-rooted-hom-Directed-Tree :
    hom-Directed-Tree R T
  hom-comp-rooted-hom-Directed-Tree =
    comp-hom-Directed-Tree R S T
      ( hom-rooted-hom-Directed-Tree S T g)
      ( hom-rooted-hom-Directed-Tree R S f)

  preserves-root-comp-rooted-hom-Directed-Tree :
    preserves-root-hom-Directed-Tree R T hom-comp-rooted-hom-Directed-Tree
  preserves-root-comp-rooted-hom-Directed-Tree =
    ( preserves-root-rooted-hom-Directed-Tree S T g) ∙
    ( ap
      ( node-rooted-hom-Directed-Tree S T g)
      ( preserves-root-rooted-hom-Directed-Tree R S f))
  
  comp-rooted-hom-Directed-Tree :
    rooted-hom-Directed-Tree R T
  pr1 comp-rooted-hom-Directed-Tree = hom-comp-rooted-hom-Directed-Tree
  pr2 comp-rooted-hom-Directed-Tree =
    preserves-root-comp-rooted-hom-Directed-Tree
```
