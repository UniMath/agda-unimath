# Enriched directed trees

```agda
module trees.enriched-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import trees.directed-trees
```

</details>

## Idea

Consider a type `A` and a type family `B` over `A`. An
`(A,B)`-{{#concept "enriched directed tree" Agda=Enriched-Directed-Tree}} is a
[directed tree](trees.directed-trees.md) `T` [equipped](foundation.structure.md)
with a map

```text
  shape : node-Directed-Tree T → A
```

and for each node `x` an [equivalence](foundation-core.equivalences.md)

```text
  e : B (shape x) ≃ Σ (node-Directed-Tree T) (λ y → edge-Directed-Tree T y x)
```

By this equivalence, there is a higher group action of `Ω (A , f x)` on the type
of children of `x`.

## Definition

```agda
Enriched-Directed-Tree :
  {l1 l2 : Level} (l3 l4 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
Enriched-Directed-Tree l3 l4 A B =
  Σ ( Directed-Tree l3 l4)
    ( λ T →
      Σ ( node-Directed-Tree T → A)
        ( λ f →
          (x : node-Directed-Tree T) →
          B (f x) ≃
          Σ (node-Directed-Tree T) (λ y → edge-Directed-Tree T y x)))

module _
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2)
  (T : Enriched-Directed-Tree l3 l4 A B)
  where

  directed-tree-Enriched-Directed-Tree : Directed-Tree l3 l4
  directed-tree-Enriched-Directed-Tree = pr1 T

  graph-Enriched-Directed-Tree : Directed-Graph l3 l4
  graph-Enriched-Directed-Tree =
    graph-Directed-Tree directed-tree-Enriched-Directed-Tree

  node-Enriched-Directed-Tree : UU l3
  node-Enriched-Directed-Tree =
    node-Directed-Tree directed-tree-Enriched-Directed-Tree

  edge-Enriched-Directed-Tree :
    (x y : node-Enriched-Directed-Tree) → UU l4
  edge-Enriched-Directed-Tree =
    edge-Directed-Tree directed-tree-Enriched-Directed-Tree

  direct-predecessor-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree → UU (l3 ⊔ l4)
  direct-predecessor-Enriched-Directed-Tree =
    direct-predecessor-Directed-Tree directed-tree-Enriched-Directed-Tree

  node-direct-predecessor-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    direct-predecessor-Enriched-Directed-Tree x → node-Enriched-Directed-Tree
  node-direct-predecessor-Enriched-Directed-Tree =
    node-direct-predecessor-Directed-Tree directed-tree-Enriched-Directed-Tree

  edge-direct-predecessor-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree)
    (y : direct-predecessor-Enriched-Directed-Tree x) →
    edge-Enriched-Directed-Tree
      ( node-direct-predecessor-Enriched-Directed-Tree x y)
      ( x)
  edge-direct-predecessor-Enriched-Directed-Tree =
    edge-direct-predecessor-Directed-Tree directed-tree-Enriched-Directed-Tree

  walk-Enriched-Directed-Tree :
    (x y : node-Enriched-Directed-Tree) → UU (l3 ⊔ l4)
  walk-Enriched-Directed-Tree =
    walk-Directed-Tree directed-tree-Enriched-Directed-Tree

  refl-walk-Enriched-Directed-Tree :
    {x : node-Enriched-Directed-Tree} → walk-Enriched-Directed-Tree x x
  refl-walk-Enriched-Directed-Tree =
    refl-walk-Directed-Tree directed-tree-Enriched-Directed-Tree

  cons-walk-Enriched-Directed-Tree :
    {x y z : node-Enriched-Directed-Tree} → edge-Enriched-Directed-Tree x y →
    walk-Enriched-Directed-Tree y z → walk-Enriched-Directed-Tree x z
  cons-walk-Enriched-Directed-Tree =
    cons-walk-Directed-Tree directed-tree-Enriched-Directed-Tree

  unit-walk-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree} →
    edge-Enriched-Directed-Tree x y → walk-Enriched-Directed-Tree x y
  unit-walk-Enriched-Directed-Tree =
    unit-walk-Directed-Tree directed-tree-Enriched-Directed-Tree

  length-walk-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree} →
    walk-Enriched-Directed-Tree x y → ℕ
  length-walk-Enriched-Directed-Tree =
    length-walk-Directed-Tree directed-tree-Enriched-Directed-Tree

  root-Enriched-Directed-Tree : node-Enriched-Directed-Tree
  root-Enriched-Directed-Tree =
    root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-root-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree → UU l3
  is-root-Enriched-Directed-Tree =
    is-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-isolated-root-Enriched-Directed-Tree :
    is-isolated root-Enriched-Directed-Tree
  is-isolated-root-Enriched-Directed-Tree =
    is-isolated-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-prop-is-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-prop (is-root-Enriched-Directed-Tree x)
  is-prop-is-root-Enriched-Directed-Tree =
    is-prop-is-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-root-enriched-directed-tree-Prop :
    (x : node-Enriched-Directed-Tree) → Prop l3
  is-root-enriched-directed-tree-Prop =
    is-root-directed-tree-Prop directed-tree-Enriched-Directed-Tree

  is-contr-loop-space-root-Enriched-Directed-Tree :
    is-contr (root-Enriched-Directed-Tree ＝ root-Enriched-Directed-Tree)
  is-contr-loop-space-root-Enriched-Directed-Tree =
    is-contr-loop-space-root-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  is-proper-node-Enriched-Directed-Tree :
    node-Enriched-Directed-Tree → UU l3
  is-proper-node-Enriched-Directed-Tree =
    is-proper-node-Directed-Tree directed-tree-Enriched-Directed-Tree

  eq-refl-root-Enriched-Directed-Tree :
    (p : root-Enriched-Directed-Tree ＝ root-Enriched-Directed-Tree) → p ＝ refl
  eq-refl-root-Enriched-Directed-Tree =
    eq-refl-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  eq-refl-root-Enriched-Directed-Tree' :
    (p : root-Enriched-Directed-Tree ＝ root-Enriched-Directed-Tree) → refl ＝ p
  eq-refl-root-Enriched-Directed-Tree' =
    eq-refl-root-Directed-Tree' directed-tree-Enriched-Directed-Tree

  no-direct-successor-root-Enriched-Directed-Tree :
    ¬ ( Σ ( node-Enriched-Directed-Tree)
          ( edge-Enriched-Directed-Tree root-Enriched-Directed-Tree))
  no-direct-successor-root-Enriched-Directed-Tree =
    no-direct-successor-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-proper-node-direct-successor-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree} (e : edge-Enriched-Directed-Tree x y) →
    ¬ (is-root-Enriched-Directed-Tree x)
  is-proper-node-direct-successor-Enriched-Directed-Tree =
    is-proper-node-direct-successor-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  is-proof-irrelevant-edge-to-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-proof-irrelevant
      ( edge-Enriched-Directed-Tree x root-Enriched-Directed-Tree)
  is-proof-irrelevant-edge-to-root-Enriched-Directed-Tree =
    is-proof-irrelevant-edge-to-root-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  is-prop-edge-to-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-prop (edge-Enriched-Directed-Tree x root-Enriched-Directed-Tree)
  is-prop-edge-to-root-Enriched-Directed-Tree =
    is-prop-edge-to-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  is-tree-Enriched-Directed-Tree :
    is-tree-Directed-Graph graph-Enriched-Directed-Tree
  is-tree-Enriched-Directed-Tree =
    is-tree-Directed-Tree directed-tree-Enriched-Directed-Tree

  unique-walk-to-root-Enriched-Directed-Tree :
    is-tree-Directed-Graph'
      graph-Enriched-Directed-Tree
      root-Enriched-Directed-Tree
  unique-walk-to-root-Enriched-Directed-Tree =
    unique-walk-to-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  uniqueness-root-Enriched-Directed-Tree :
    (H : is-tree-Directed-Graph graph-Enriched-Directed-Tree) →
    is-root-Enriched-Directed-Tree (pr1 H)
  uniqueness-root-Enriched-Directed-Tree =
    uniqueness-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  walk-to-root-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    walk-Enriched-Directed-Tree x root-Enriched-Directed-Tree
  walk-to-root-Enriched-Directed-Tree =
    walk-to-root-Directed-Tree directed-tree-Enriched-Directed-Tree

  unique-direct-successor-Enriched-Directed-Tree :
    unique-direct-successor-Directed-Graph
      graph-Enriched-Directed-Tree
      root-Enriched-Directed-Tree
  unique-direct-successor-Enriched-Directed-Tree =
    unique-direct-successor-Directed-Tree directed-tree-Enriched-Directed-Tree

  unique-direct-successor-is-proper-node-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-proper-node-Enriched-Directed-Tree x →
    is-contr ( Σ node-Enriched-Directed-Tree (edge-Enriched-Directed-Tree x))
  unique-direct-successor-is-proper-node-Enriched-Directed-Tree =
    unique-direct-successor-is-proper-node-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  is-proof-irrelevant-direct-successor-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-proof-irrelevant
      ( Σ (node-Enriched-Directed-Tree) (edge-Enriched-Directed-Tree x))
  is-proof-irrelevant-direct-successor-Enriched-Directed-Tree =
    is-proof-irrelevant-direct-successor-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  is-prop-direct-successor-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    is-prop
      ( Σ (node-Enriched-Directed-Tree) (edge-Enriched-Directed-Tree x))
  is-prop-direct-successor-Enriched-Directed-Tree =
    is-prop-direct-successor-Directed-Tree directed-tree-Enriched-Directed-Tree

  eq-direct-successor-Enriched-Directed-Tree :
    {x : node-Enriched-Directed-Tree}
    ( u v : Σ (node-Enriched-Directed-Tree) (edge-Enriched-Directed-Tree x)) →
    u ＝ v
  eq-direct-successor-Enriched-Directed-Tree =
    eq-direct-successor-Directed-Tree directed-tree-Enriched-Directed-Tree

  direct-successor-is-proper-node-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    ¬ (is-root-Enriched-Directed-Tree x) →
    Σ (node-Enriched-Directed-Tree) (edge-Enriched-Directed-Tree x)
  direct-successor-is-proper-node-Enriched-Directed-Tree =
    direct-successor-is-proper-node-Directed-Tree
      directed-tree-Enriched-Directed-Tree

  shape-Enriched-Directed-Tree : node-Enriched-Directed-Tree → A
  shape-Enriched-Directed-Tree = pr1 (pr2 T)

  shape-root-Enriched-Directed-Tree : A
  shape-root-Enriched-Directed-Tree =
    shape-Enriched-Directed-Tree root-Enriched-Directed-Tree

  enrichment-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    B (shape-Enriched-Directed-Tree x) ≃
    Σ (node-Enriched-Directed-Tree) (λ y → edge-Enriched-Directed-Tree y x)
  enrichment-Enriched-Directed-Tree = pr2 (pr2 T)

  map-enrichment-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) →
    B (shape-Enriched-Directed-Tree x) →
    direct-predecessor-Enriched-Directed-Tree x
  map-enrichment-Enriched-Directed-Tree x =
    map-equiv (enrichment-Enriched-Directed-Tree x)

  node-enrichment-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) (b : B (shape-Enriched-Directed-Tree x)) →
    node-Enriched-Directed-Tree
  node-enrichment-Enriched-Directed-Tree x b =
    pr1 (map-enrichment-Enriched-Directed-Tree x b)

  edge-enrichment-Enriched-Directed-Tree :
    (x : node-Enriched-Directed-Tree) (b : B (shape-Enriched-Directed-Tree x)) →
    edge-Enriched-Directed-Tree (node-enrichment-Enriched-Directed-Tree x b) x
  edge-enrichment-Enriched-Directed-Tree x b =
    pr2 (map-enrichment-Enriched-Directed-Tree x b)

  coherence-square-map-enrichment-Enriched-Directed-Tree :
    {x y : node-Enriched-Directed-Tree} (p : x ＝ y) →
    coherence-square-maps
      ( tr B (ap shape-Enriched-Directed-Tree p))
      ( map-enrichment-Enriched-Directed-Tree x)
      ( map-enrichment-Enriched-Directed-Tree y)
      ( tot ( λ y → tr (edge-Enriched-Directed-Tree y) p))
  coherence-square-map-enrichment-Enriched-Directed-Tree refl = refl-htpy
```
