# Bases of directed trees

```agda
module trees.bases-directed-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import graph-theory.walks-directed-graphs

open import trees.directed-trees
```

</details>

## Idea

The
{{#concept "base" Disambiguation="of a directed tree" Agda=base-Directed-Tree}}
of a [directed tree](trees.directed-trees.md) consists of the nodes equipped
with an edge to the root.

## Definition

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  base-Directed-Tree : UU (l1 ⊔ l2)
  base-Directed-Tree = direct-predecessor-Directed-Tree T (root-Directed-Tree T)

  module _
    (b : base-Directed-Tree)
    where

    node-base-Directed-Tree : node-Directed-Tree T
    node-base-Directed-Tree = pr1 b

    edge-base-Directed-Tree :
      edge-Directed-Tree T node-base-Directed-Tree (root-Directed-Tree T)
    edge-base-Directed-Tree = pr2 b
```

## Properties

### The root is not a base element

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proper-node-base-Directed-Tree :
    (b : base-Directed-Tree T) →
    is-proper-node-Directed-Tree T (node-base-Directed-Tree T b)
  is-proper-node-base-Directed-Tree (x , e) refl =
    no-direct-successor-root-Directed-Tree T (x , e)

  no-walk-to-base-root-Directed-Tree :
    (b : base-Directed-Tree T) →
    ¬ ( walk-Directed-Tree T
        ( root-Directed-Tree T)
        ( node-base-Directed-Tree T b))
  no-walk-to-base-root-Directed-Tree
    ( pair .(root-Directed-Tree T) e)
    refl-walk-Directed-Graph =
    no-direct-successor-root-Directed-Tree T (root-Directed-Tree T , e)
  no-walk-to-base-root-Directed-Tree b (cons-walk-Directed-Graph e w) =
    no-direct-successor-root-Directed-Tree T (_ , e)
```

### Any node which has a walk to a base element is a proper node

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  is-proper-node-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) (b : base-Directed-Tree T) →
    walk-Directed-Tree T x (node-base-Directed-Tree T b) →
    is-proper-node-Directed-Tree T x
  is-proper-node-walk-to-base-Directed-Tree ._ b refl-walk-Directed-Graph =
    is-proper-node-base-Directed-Tree T b
  is-proper-node-walk-to-base-Directed-Tree x b (cons-walk-Directed-Graph e w) =
    is-proper-node-direct-successor-Directed-Tree T e
```

### There are no edges between base elements

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  no-edge-base-Directed-Tree :
    (a b : base-Directed-Tree T) →
    ¬ ( edge-Directed-Tree T
        ( node-base-Directed-Tree T a)
        ( node-base-Directed-Tree T b))
  no-edge-base-Directed-Tree a b e =
    ex-falso
      ( is-not-one-two-ℕ
        ( ap
          ( length-walk-Directed-Graph (graph-Directed-Tree T))
          ( eq-is-contr'
            ( unique-walk-to-root-Directed-Tree T
              ( node-base-Directed-Tree T a))
            ( cons-walk-Directed-Tree T e
              ( unit-walk-Directed-Tree T (edge-base-Directed-Tree T b)))
            ( unit-walk-Directed-Tree T (edge-base-Directed-Tree T a)))))
```

### For any node `x`, the coproduct of `is-root x` and the type of base elements `b` equipped with a walk from `x` to `b` is contractible

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  cons-cases-center-walk-to-base-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    (w : walk-Directed-Tree T y (root-Directed-Tree T)) →
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  cons-cases-center-walk-to-base-Directed-Tree e refl-walk-Directed-Graph =
    (_ , e) , refl-walk-Directed-Tree T
  cons-cases-center-walk-to-base-Directed-Tree e
    ( cons-walk-Directed-Graph f w) =
    tot
      ( λ u → cons-walk-Directed-Tree T e)
      ( cons-cases-center-walk-to-base-Directed-Tree f w)

  cases-center-walk-to-base-Directed-Tree :
    {x : node-Directed-Tree T}
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    is-root-Directed-Tree T x +
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  cases-center-walk-to-base-Directed-Tree refl-walk-Directed-Graph = inl refl
  cases-center-walk-to-base-Directed-Tree (cons-walk-Directed-Graph e w) =
    inr (cons-cases-center-walk-to-base-Directed-Tree e w)

  center-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)
  center-walk-to-base-Directed-Tree x =
    cases-center-walk-to-base-Directed-Tree (walk-to-root-Directed-Tree T x)

  cons-cases-contraction-walk-to-base-Directed-Tree :
    {x y : node-Directed-Tree T} (e : edge-Directed-Tree T x y) →
    (w : walk-Directed-Tree T y (root-Directed-Tree T))
    (u : Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    cons-cases-center-walk-to-base-Directed-Tree e w ＝ u
  cons-cases-contraction-walk-to-base-Directed-Tree e
    ( refl-walk-Directed-Graph)
    ( (z , f) , refl-walk-Directed-Graph) =
    ap
      ( λ i → ((z , i) , refl-walk-Directed-Graph))
      ( eq-is-contr
        ( is-proof-irrelevant-edge-to-root-Directed-Tree T z e))
  cons-cases-contraction-walk-to-base-Directed-Tree {x} e
    ( refl-walk-Directed-Graph)
    ( (z , f) , cons-walk-Directed-Graph {_} {y} g v) =
    ex-falso
      ( no-walk-to-base-root-Directed-Tree T
        ( z , f)
        ( tr
          ( λ u → walk-Directed-Tree T u z)
          ( ap pr1
            ( eq-direct-successor-Directed-Tree T
              ( y , g)
              ( root-Directed-Tree T , e)))
          ( v)))
  cons-cases-contraction-walk-to-base-Directed-Tree e
    ( cons-walk-Directed-Graph {y} {z} g w)
    ( (u , f) , refl-walk-Directed-Graph) =
    ex-falso
      ( no-direct-successor-root-Directed-Tree T
        ( tr
          ( λ i → Σ (node-Directed-Tree T) (edge-Directed-Tree T i))
          ( ap pr1
            ( eq-direct-successor-Directed-Tree T
              ( y , e)
              ( root-Directed-Tree T , f)))
          ( z , g)))
  cons-cases-contraction-walk-to-base-Directed-Tree {x} {y} e
    ( cons-walk-Directed-Graph {y} {z} g w)
    ( (u , f) , cons-walk-Directed-Graph {_} {y'} e' v) =
    ( ap
      ( tot (λ u → cons-walk-Directed-Tree T e))
      ( cons-cases-contraction-walk-to-base-Directed-Tree g w
        ( (u , f) ,
          ( tr-walk-eq-direct-successor-Directed-Tree T
            ( y' , e')
            ( y , e) v)))) ∙
    ( ap
      ( pair (u , f))
      ( eq-tr-walk-eq-direct-successor-Directed-Tree T (y' , e') (y , e) v))

  cases-contraction-walk-to-base-Directed-Tree :
    {x : node-Directed-Tree T}
    (w : walk-Directed-Tree T x (root-Directed-Tree T)) →
    (u :
      is-root-Directed-Tree T x +
      Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    cases-center-walk-to-base-Directed-Tree w ＝ u
  cases-contraction-walk-to-base-Directed-Tree
    ( refl-walk-Directed-Graph)
    ( inl p) =
    ap inl (eq-is-contr (is-contr-loop-space-root-Directed-Tree T))
  cases-contraction-walk-to-base-Directed-Tree refl-walk-Directed-Graph
    ( inr (b , w)) =
    ex-falso (no-walk-to-base-root-Directed-Tree T b w)
  cases-contraction-walk-to-base-Directed-Tree
    ( cons-walk-Directed-Graph e w)
    ( inl refl) =
    ex-falso (no-direct-successor-root-Directed-Tree T (_ , e))
  cases-contraction-walk-to-base-Directed-Tree
    ( cons-walk-Directed-Graph e w) (inr u) =
    ap inr (cons-cases-contraction-walk-to-base-Directed-Tree e w u)

  contraction-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T)
    ( w :
      is-root-Directed-Tree T x +
      Σ (base-Directed-Tree T) (walk-Directed-Tree T x ∘ pr1)) →
    center-walk-to-base-Directed-Tree x ＝ w
  contraction-walk-to-base-Directed-Tree x =
    cases-contraction-walk-to-base-Directed-Tree
      ( walk-to-root-Directed-Tree T x)

  unique-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-contr
      ( is-root-Directed-Tree T x +
        Σ ( base-Directed-Tree T)
          ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T))
  unique-walk-to-base-Directed-Tree x =
    ( center-walk-to-base-Directed-Tree x ,
      contraction-walk-to-base-Directed-Tree x)

  is-root-or-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-root-Directed-Tree T x +
    Σ ( base-Directed-Tree T)
      ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T)
  is-root-or-walk-to-base-Directed-Tree x =
    center (unique-walk-to-base-Directed-Tree x)

  is-root-is-root-or-walk-to-base-root-Directed-Tree :
    is-root-or-walk-to-base-Directed-Tree (root-Directed-Tree T) ＝
    inl refl
  is-root-is-root-or-walk-to-base-root-Directed-Tree =
    eq-is-contr (unique-walk-to-base-Directed-Tree (root-Directed-Tree T))

  unique-walk-to-base-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    is-contr
      ( Σ ( base-Directed-Tree T)
          ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T))
  unique-walk-to-base-is-proper-node-Directed-Tree x f =
    is-contr-equiv'
      ( is-root-Directed-Tree T x +
        Σ ( base-Directed-Tree T)
          ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T))
      ( left-unit-law-coproduct-is-empty
        ( is-root-Directed-Tree T x)
        ( Σ ( base-Directed-Tree T)
          ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T))
        ( f))
      ( unique-walk-to-base-Directed-Tree x)

  walk-to-base-is-proper-node-Directed-Tree :
    (x : node-Directed-Tree T) → is-proper-node-Directed-Tree T x →
    Σ ( base-Directed-Tree T)
      ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T)
  walk-to-base-is-proper-node-Directed-Tree x H =
    center (unique-walk-to-base-is-proper-node-Directed-Tree x H)

  unique-walk-to-base-direct-successor-Directed-Tree :
    (x : node-Directed-Tree T)
    (u : Σ (node-Directed-Tree T) (edge-Directed-Tree T x)) →
    is-contr
      ( Σ ( base-Directed-Tree T)
          ( walk-Directed-Tree T x ∘ node-base-Directed-Tree T))
  unique-walk-to-base-direct-successor-Directed-Tree x u =
    unique-walk-to-base-is-proper-node-Directed-Tree x
      ( is-proper-node-direct-successor-Directed-Tree T (pr2 u))

  is-proof-irrelevant-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-proof-irrelevant
      ( Σ ( base-Directed-Tree T)
          ( λ b → walk-Directed-Tree T x (node-base-Directed-Tree T b)))
  is-proof-irrelevant-walk-to-base-Directed-Tree x (b , w) =
    unique-walk-to-base-is-proper-node-Directed-Tree x
      ( is-proper-node-walk-to-base-Directed-Tree T x b w)

  is-prop-walk-to-base-Directed-Tree :
    (x : node-Directed-Tree T) →
    is-prop
      ( Σ ( base-Directed-Tree T)
          ( λ b → walk-Directed-Tree T x (node-base-Directed-Tree T b)))
  is-prop-walk-to-base-Directed-Tree x =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-walk-to-base-Directed-Tree x)

  walk-to-base-Directed-Tree-Prop : node-Directed-Tree T → Prop (l1 ⊔ l2)
  pr1 (walk-to-base-Directed-Tree-Prop x) =
    Σ ( base-Directed-Tree T)
      ( λ b → walk-Directed-Tree T x (node-base-Directed-Tree T b))
  pr2 (walk-to-base-Directed-Tree-Prop x) =
    is-prop-walk-to-base-Directed-Tree x
```

### The type of proper nodes of a directed tree is equivalent to the type of nodes equipped with a base element `b` and a walk to `b`

```agda
module _
  {l1 l2 : Level} (T : Directed-Tree l1 l2)
  where

  compute-proper-node-Directed-Tree :
    proper-node-Directed-Tree T ≃
    Σ ( base-Directed-Tree T)
      ( λ b →
        Σ ( node-Directed-Tree T)
          ( λ x → walk-Directed-Tree T x (node-base-Directed-Tree T b)))
  compute-proper-node-Directed-Tree =
    ( equiv-left-swap-Σ) ∘e
    ( equiv-tot
      ( λ x →
        equiv-iff
          ( is-proper-node-Directed-Tree-Prop T x)
          ( walk-to-base-Directed-Tree-Prop T x)
          ( walk-to-base-is-proper-node-Directed-Tree T x)
          ( λ (b , w) → is-proper-node-walk-to-base-Directed-Tree T x b w)))

  map-compute-proper-node-Directed-Tree :
    proper-node-Directed-Tree T →
    Σ ( base-Directed-Tree T)
      ( λ b →
        Σ ( node-Directed-Tree T)
          ( λ x → walk-Directed-Tree T x (node-base-Directed-Tree T b)))
  map-compute-proper-node-Directed-Tree =
    map-equiv compute-proper-node-Directed-Tree

  eq-compute-proper-node-Directed-Tree :
    {x : node-Directed-Tree T} (H : is-proper-node-Directed-Tree T x)
    (b : base-Directed-Tree T)
    (w : walk-Directed-Tree T x (node-base-Directed-Tree T b)) →
    map-compute-proper-node-Directed-Tree (x , H) ＝ (b , x , w)
  eq-compute-proper-node-Directed-Tree {x} H b w =
    ap
      ( map-equiv equiv-left-swap-Σ)
      ( eq-pair-eq-fiber (eq-is-prop (is-prop-walk-to-base-Directed-Tree T x)))
```
