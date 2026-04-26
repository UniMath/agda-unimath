# Bases of enriched directed trees

```agda
module trees.bases-enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import trees.bases-directed-trees
open import trees.enriched-directed-trees
```

</details>

## Idea

The
{{#concept "base" Disambiguation="of an enriched directed tree" Agda=base-Enriched-Directed-Tree}}
of an [enriched directed tree](trees.enriched-directed-trees.md) consists of its
nodes equipped with an edge to the root.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  base-Enriched-Directed-Tree : UU l2
  base-Enriched-Directed-Tree = B (shape-root-Enriched-Directed-Tree A B T)

  compute-base-Enriched-Directed-Tree :
    base-Enriched-Directed-Tree ≃
    direct-predecessor-Enriched-Directed-Tree A B T
      ( root-Enriched-Directed-Tree A B T)
  compute-base-Enriched-Directed-Tree =
    enrichment-Enriched-Directed-Tree A B T (root-Enriched-Directed-Tree A B T)

  map-compute-base-Enriched-Directed-Tree :
    base-Enriched-Directed-Tree →
    direct-predecessor-Enriched-Directed-Tree A B T
      ( root-Enriched-Directed-Tree A B T)
  map-compute-base-Enriched-Directed-Tree =
    map-enrichment-Enriched-Directed-Tree A B T
      ( root-Enriched-Directed-Tree A B T)

  module _
    (b : base-Enriched-Directed-Tree)
    where

    node-base-Enriched-Directed-Tree : node-Enriched-Directed-Tree A B T
    node-base-Enriched-Directed-Tree =
      node-base-Directed-Tree
        ( directed-tree-Enriched-Directed-Tree A B T)
        ( map-compute-base-Enriched-Directed-Tree b)

    edge-base-Enriched-Directed-Tree :
      edge-Enriched-Directed-Tree A B T
        ( node-base-Enriched-Directed-Tree)
        ( root-Enriched-Directed-Tree A B T)
    edge-base-Enriched-Directed-Tree =
      edge-base-Directed-Tree
        ( directed-tree-Enriched-Directed-Tree A B T)
        ( map-compute-base-Enriched-Directed-Tree b)
```

## Properties

### The root is not a base element

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  is-proper-node-base-Enriched-Directed-Tree :
    (b : base-Enriched-Directed-Tree A B T) →
    is-proper-node-Enriched-Directed-Tree A B T
      ( node-base-Enriched-Directed-Tree A B T b)
  is-proper-node-base-Enriched-Directed-Tree b =
    is-proper-node-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( map-compute-base-Enriched-Directed-Tree A B T b)

  no-walk-to-base-root-Enriched-Directed-Tree :
    (b : base-Enriched-Directed-Tree A B T) →
    ¬ ( walk-Enriched-Directed-Tree A B T
        ( root-Enriched-Directed-Tree A B T)
        ( node-base-Enriched-Directed-Tree A B T b))
  no-walk-to-base-root-Enriched-Directed-Tree b =
    no-walk-to-base-root-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( map-compute-base-Enriched-Directed-Tree A B T b)
```

### There are no edges between base elements

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  no-edge-base-Enriched-Directed-Tree :
    (a b : base-Enriched-Directed-Tree A B T) →
    ¬ ( edge-Enriched-Directed-Tree A B T
        ( node-base-Enriched-Directed-Tree A B T a)
        ( node-base-Enriched-Directed-Tree A B T b))
  no-edge-base-Enriched-Directed-Tree a b =
    no-edge-base-Directed-Tree
      ( directed-tree-Enriched-Directed-Tree A B T)
      ( map-compute-base-Enriched-Directed-Tree A B T a)
      ( map-compute-base-Enriched-Directed-Tree A B T b)
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  unique-walk-to-base-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    is-contr
      ( is-root-Enriched-Directed-Tree A B T x +
        Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-Enriched-Directed-Tree x =
    is-contr-equiv
      ( is-root-Enriched-Directed-Tree A B T x +
        Σ ( direct-predecessor-Enriched-Directed-Tree A B T
            ( root-Enriched-Directed-Tree A B T))
          ( walk-Enriched-Directed-Tree A B T x ∘ pr1))
      ( equiv-coproduct
        ( id-equiv)
        ( equiv-Σ
          ( walk-Enriched-Directed-Tree A B T x ∘ pr1)
          ( compute-base-Enriched-Directed-Tree A B T)
          ( λ b → id-equiv)))
      ( unique-walk-to-base-Directed-Tree
        ( directed-tree-Enriched-Directed-Tree A B T)
        ( x))

  is-root-or-walk-to-base-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    is-root-Enriched-Directed-Tree A B T x +
    Σ ( base-Enriched-Directed-Tree A B T)
      ( walk-Enriched-Directed-Tree A B T x ∘
        node-base-Enriched-Directed-Tree A B T)
  is-root-or-walk-to-base-Enriched-Directed-Tree x =
    center (unique-walk-to-base-Enriched-Directed-Tree x)

  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Tree :
    is-root-or-walk-to-base-Enriched-Directed-Tree
      ( root-Enriched-Directed-Tree A B T) ＝
    inl refl
  is-root-is-root-or-walk-to-base-root-Enriched-Directed-Tree =
    eq-is-contr
      ( unique-walk-to-base-Enriched-Directed-Tree
        ( root-Enriched-Directed-Tree A B T))

  unique-walk-to-base-is-not-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T) →
    ¬ (is-root-Enriched-Directed-Tree A B T x) →
    is-contr
      ( Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-is-not-root-Enriched-Directed-Tree x f =
    is-contr-equiv'
      ( is-root-Enriched-Directed-Tree A B T x +
        Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
      ( left-unit-law-coproduct-is-empty
        ( is-root-Enriched-Directed-Tree A B T x)
        ( Σ ( base-Enriched-Directed-Tree A B T)
            ( walk-Enriched-Directed-Tree A B T x ∘
              node-base-Enriched-Directed-Tree A B T))
        ( f))
      ( unique-walk-to-base-Enriched-Directed-Tree x)

  unique-walk-to-base-direct-successor-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree A B T)
    (u :
      Σ ( node-Enriched-Directed-Tree A B T)
        ( edge-Enriched-Directed-Tree A B T x)) →
    is-contr
      ( Σ ( base-Enriched-Directed-Tree A B T)
          ( walk-Enriched-Directed-Tree A B T x ∘
            node-base-Enriched-Directed-Tree A B T))
  unique-walk-to-base-direct-successor-Enriched-Directed-Tree x (y , e) =
    unique-walk-to-base-is-not-root-Enriched-Directed-Tree x
      ( is-proper-node-direct-successor-Enriched-Directed-Tree A B T e)
```
