# Rooted morphisms of directed trees

```agda
module trees.rooted-morphisms-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.bases-directed-trees
open import trees.directed-trees
open import trees.morphisms-directed-trees
```

</details>

## Idea

A
{{#concept "rooted morphism" Disambiguation="of directed trees" Agda=rooted-hom-Directed-Tree}}
of [directed trees](trees.directed-trees.md) from `S` to `T` is a
[morphism](trees.morphisms-directed-trees.md) of directed trees that maps the
root of `S` to the root of `T`.

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

    walk-rooted-hom-Directed-Tree :
      {x y : node-Directed-Tree S} →
      walk-Directed-Tree S x y →
      walk-Directed-Tree T
        ( node-rooted-hom-Directed-Tree x)
        ( node-rooted-hom-Directed-Tree y)
    walk-rooted-hom-Directed-Tree =
      walk-hom-Directed-Tree S T hom-rooted-hom-Directed-Tree

    direct-predecessor-rooted-hom-Directed-Tree :
      (x : node-Directed-Tree S) →
      direct-predecessor-Directed-Tree S x →
      direct-predecessor-Directed-Tree T (node-rooted-hom-Directed-Tree x)
    direct-predecessor-rooted-hom-Directed-Tree =
      direct-predecessor-hom-Directed-Tree S T hom-rooted-hom-Directed-Tree

    preserves-root-rooted-hom-Directed-Tree :
      preserves-root-hom-Directed-Tree hom-rooted-hom-Directed-Tree
    preserves-root-rooted-hom-Directed-Tree = pr2 f

    base-rooted-hom-Directed-Tree :
      base-Directed-Tree S → base-Directed-Tree T
    base-rooted-hom-Directed-Tree (x , e) =
      node-rooted-hom-Directed-Tree x ,
      tr
        ( edge-Directed-Tree T (node-rooted-hom-Directed-Tree x))
        ( inv preserves-root-rooted-hom-Directed-Tree)
        ( edge-rooted-hom-Directed-Tree e)
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

### Homotopies of rooted morphisms of directed trees

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  where

  htpy-rooted-hom-Directed-Tree :
    (f g : rooted-hom-Directed-Tree S T) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-rooted-hom-Directed-Tree f g =
    htpy-hom-Directed-Tree S T
      ( hom-rooted-hom-Directed-Tree S T f)
      ( hom-rooted-hom-Directed-Tree S T g)

  refl-htpy-rooted-hom-Directed-Tree :
    (f : rooted-hom-Directed-Tree S T) →
    htpy-rooted-hom-Directed-Tree f f
  refl-htpy-rooted-hom-Directed-Tree f =
    refl-htpy-hom-Directed-Tree S T (hom-rooted-hom-Directed-Tree S T f)

  module _
    (f g : rooted-hom-Directed-Tree S T)
    (H : htpy-rooted-hom-Directed-Tree f g)
    where

    node-htpy-rooted-hom-Directed-Tree :
      node-rooted-hom-Directed-Tree S T f ~ node-rooted-hom-Directed-Tree S T g
    node-htpy-rooted-hom-Directed-Tree =
      node-htpy-hom-Directed-Tree S T
        ( hom-rooted-hom-Directed-Tree S T f)
        ( hom-rooted-hom-Directed-Tree S T g)
        ( H)

    edge-htpy-rooted-hom-Directed-Tree :
      ( x y : node-Directed-Tree S) (e : edge-Directed-Tree S x y) →
      binary-tr
        ( edge-Directed-Tree T)
        ( node-htpy-rooted-hom-Directed-Tree x)
        ( node-htpy-rooted-hom-Directed-Tree y)
        ( edge-rooted-hom-Directed-Tree S T f e) ＝
      edge-rooted-hom-Directed-Tree S T g e
    edge-htpy-rooted-hom-Directed-Tree =
      edge-htpy-hom-Directed-Tree S T
        ( hom-rooted-hom-Directed-Tree S T f)
        ( hom-rooted-hom-Directed-Tree S T g)
        ( H)

    direct-predecessor-htpy-rooted-hom-Directed-Tree :
      ( x : node-Directed-Tree S) →
      ( ( tot
          ( λ y →
            tr
              ( edge-Directed-Tree T y)
              ( node-htpy-rooted-hom-Directed-Tree x))) ∘
        ( direct-predecessor-rooted-hom-Directed-Tree S T f x)) ~
      ( direct-predecessor-rooted-hom-Directed-Tree S T g x)
    direct-predecessor-htpy-rooted-hom-Directed-Tree =
      direct-predecessor-htpy-hom-Directed-Tree S T
        ( hom-rooted-hom-Directed-Tree S T f)
        ( hom-rooted-hom-Directed-Tree S T g)
        ( H)
```

## Properties

### Homotopies of rooted morphisms characterize identifications of rooted morphisms

```agda
module _
  {l1 l2 l3 l4 : Level} (S : Directed-Tree l1 l2) (T : Directed-Tree l3 l4)
  (f : rooted-hom-Directed-Tree S T)
  where

  extensionality-rooted-hom-Directed-Tree :
    (g : rooted-hom-Directed-Tree S T) →
    (f ＝ g) ≃ htpy-rooted-hom-Directed-Tree S T f g
  extensionality-rooted-hom-Directed-Tree =
    extensionality-type-subtype
      ( preserves-root-hom-directed-tree-Prop S T)
      ( preserves-root-rooted-hom-Directed-Tree S T f)
      ( refl-htpy-rooted-hom-Directed-Tree S T f)
      ( extensionality-hom-Directed-Tree S T
        ( hom-rooted-hom-Directed-Tree S T f))

  htpy-eq-rooted-hom-Directed-Tree :
    (g : rooted-hom-Directed-Tree S T) →
    (f ＝ g) → htpy-rooted-hom-Directed-Tree S T f g
  htpy-eq-rooted-hom-Directed-Tree g =
    map-equiv (extensionality-rooted-hom-Directed-Tree g)

  eq-htpy-rooted-hom-Directed-Tree :
    (g : rooted-hom-Directed-Tree S T) →
    htpy-rooted-hom-Directed-Tree S T f g → f ＝ g
  eq-htpy-rooted-hom-Directed-Tree g =
    map-inv-equiv (extensionality-rooted-hom-Directed-Tree g)

  is-torsorial-htpy-rooted-hom-Directed-Tree :
    is-torsorial (htpy-rooted-hom-Directed-Tree S T f)
  is-torsorial-htpy-rooted-hom-Directed-Tree =
    is-contr-equiv'
      ( Σ (rooted-hom-Directed-Tree S T) (λ g → f ＝ g))
      ( equiv-tot extensionality-rooted-hom-Directed-Tree)
      ( is-torsorial-Id f)
```
