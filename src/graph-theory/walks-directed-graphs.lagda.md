---
title: Walks in directed graphs
---

```agda
module graph-theory.walks-directed-graphs where

open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.equivalences-directed-graphs
open import graph-theory.morphisms-directed-graphs
```

## Idea

A walk in a directed graph from a vertex `x` to a vertex `y` is a list of edges that connect `x` to `y`.

## Definitions

### The type of walks from `x` to `y` in `G`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  data walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2) where
    refl-walk-Directed-Graph :
      {x : vertex-Directed-Graph G} → walk-Directed-Graph x x
    cons-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} →
      edge-Directed-Graph G x y →
      walk-Directed-Graph y z → walk-Directed-Graph x z

  snoc-walk-Directed-Graph :
    {x y z : vertex-Directed-Graph G} →
    walk-Directed-Graph x y →
    edge-Directed-Graph G y z → walk-Directed-Graph x z
  snoc-walk-Directed-Graph refl-walk-Directed-Graph e =
    cons-walk-Directed-Graph e refl-walk-Directed-Graph
  snoc-walk-Directed-Graph (cons-walk-Directed-Graph f w) e =
    cons-walk-Directed-Graph f (snoc-walk-Directed-Graph w e)
```

### The type of walks of length `n` from `x` to `y` in `G`

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  walk-of-length-Directed-Graph :
    ℕ → (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
  walk-of-length-Directed-Graph zero-ℕ x y = raise l2 (y ＝ x)
  walk-of-length-Directed-Graph (succ-ℕ n) x y =
    Σ ( vertex-Directed-Graph G)
      ( λ z → edge-Directed-Graph G x z × walk-of-length-Directed-Graph n z y)

  map-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    Σ ℕ (λ n → walk-of-length-Directed-Graph n x y) → walk-Directed-Graph G x y
  map-compute-total-walk-of-length-Directed-Graph
    x .x (zero-ℕ , map-raise refl) =
    refl-walk-Directed-Graph
  map-compute-total-walk-of-length-Directed-Graph x y (succ-ℕ n , z , e , w) =
    cons-walk-Directed-Graph e
      ( map-compute-total-walk-of-length-Directed-Graph z y (n , w))

  map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y → Σ ℕ (λ n → walk-of-length-Directed-Graph n x y)
  map-inv-compute-total-walk-of-length-Directed-Graph
    x .x refl-walk-Directed-Graph =
    (0 , map-raise refl)
  map-inv-compute-total-walk-of-length-Directed-Graph x y
    ( cons-walk-Directed-Graph {y = z} e w) =
    map-Σ
      ( λ n → walk-of-length-Directed-Graph n x y)
      ( succ-ℕ)
      ( λ k u → (z , e , u))
      ( map-inv-compute-total-walk-of-length-Directed-Graph z y w)

  issec-map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-compute-total-walk-of-length-Directed-Graph x y ∘
      map-inv-compute-total-walk-of-length-Directed-Graph x y) ~ id
  issec-map-inv-compute-total-walk-of-length-Directed-Graph
    x .x refl-walk-Directed-Graph = refl
  issec-map-inv-compute-total-walk-of-length-Directed-Graph
    x y (cons-walk-Directed-Graph {y = z} e w) =
    ap
      ( cons-walk-Directed-Graph e)
      ( issec-map-inv-compute-total-walk-of-length-Directed-Graph z y w)

  isretr-map-inv-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-inv-compute-total-walk-of-length-Directed-Graph x y ∘
      map-compute-total-walk-of-length-Directed-Graph x y) ~ id
  isretr-map-inv-compute-total-walk-of-length-Directed-Graph
    x .x (zero-ℕ , map-raise refl) =
    refl
  isretr-map-inv-compute-total-walk-of-length-Directed-Graph
    x y (succ-ℕ n , (z , e , w)) =
    ap
      ( map-Σ
        ( λ n → walk-of-length-Directed-Graph n x y)
        ( succ-ℕ)
        ( λ k u → (z , e , u)))
      ( isretr-map-inv-compute-total-walk-of-length-Directed-Graph z y (n , w))

  is-equiv-map-compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    is-equiv (map-compute-total-walk-of-length-Directed-Graph x y)
  is-equiv-map-compute-total-walk-of-length-Directed-Graph x y =
    is-equiv-has-inverse
      ( map-inv-compute-total-walk-of-length-Directed-Graph x y)
      ( issec-map-inv-compute-total-walk-of-length-Directed-Graph x y)
      ( isretr-map-inv-compute-total-walk-of-length-Directed-Graph x y)

  compute-total-walk-of-length-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    Σ ℕ (λ n → walk-of-length-Directed-Graph n x y) ≃ walk-Directed-Graph G x y
  pr1 (compute-total-walk-of-length-Directed-Graph x y) =
    map-compute-total-walk-of-length-Directed-Graph x y
  pr2 (compute-total-walk-of-length-Directed-Graph x y) =
    is-equiv-map-compute-total-walk-of-length-Directed-Graph x y
```

## Properties

### The type of walks from `x` to `y` is a coproduct

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  walk-Directed-Graph' : (x y : vertex-Directed-Graph G) → UU (l1 ⊔ l2)
  walk-Directed-Graph' x y =
    (y ＝ x) +
    Σ ( vertex-Directed-Graph G)
      ( λ z → edge-Directed-Graph G x z × walk-Directed-Graph G z y)

  map-compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y → walk-Directed-Graph' x y
  map-compute-walk-Directed-Graph x .x refl-walk-Directed-Graph = inl refl
  map-compute-walk-Directed-Graph x y
    ( cons-walk-Directed-Graph {a} {b} {c} e w) =
    inr (b , e , w)

  map-inv-compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph' x y → walk-Directed-Graph G x y
  map-inv-compute-walk-Directed-Graph x .x (inl refl) =
    refl-walk-Directed-Graph
  map-inv-compute-walk-Directed-Graph x y (inr (z , e , w)) =
    cons-walk-Directed-Graph e w

  issec-map-inv-compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-compute-walk-Directed-Graph x y ∘
      map-inv-compute-walk-Directed-Graph x y) ~ id
  issec-map-inv-compute-walk-Directed-Graph x .x (inl refl) = refl
  issec-map-inv-compute-walk-Directed-Graph x y (inr (z , e , w)) = refl

  isretr-map-inv-compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    ( map-inv-compute-walk-Directed-Graph x y ∘
      map-compute-walk-Directed-Graph x y) ~ id
  isretr-map-inv-compute-walk-Directed-Graph x .x refl-walk-Directed-Graph =
    refl
  isretr-map-inv-compute-walk-Directed-Graph x y
    ( cons-walk-Directed-Graph e w) =
    refl

  is-equiv-map-compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    is-equiv (map-compute-walk-Directed-Graph x y)
  is-equiv-map-compute-walk-Directed-Graph x y =
    is-equiv-has-inverse
      ( map-inv-compute-walk-Directed-Graph x y)
      ( issec-map-inv-compute-walk-Directed-Graph x y)
      ( isretr-map-inv-compute-walk-Directed-Graph x y)

  compute-walk-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    walk-Directed-Graph G x y ≃ walk-Directed-Graph' x y
  pr1 (compute-walk-Directed-Graph x y) = map-compute-walk-Directed-Graph x y
  pr2 (compute-walk-Directed-Graph x y) =
    is-equiv-map-compute-walk-Directed-Graph x y
```

### Vertices on a walk

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  is-vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y) (v : vertex-Directed-Graph G) → UU l1
  is-vertex-on-walk-Directed-Graph {x} refl-walk-Directed-Graph v = v ＝ x
  is-vertex-on-walk-Directed-Graph {x} (cons-walk-Directed-Graph e w) v =
    ( v ＝ x) +
    ( is-vertex-on-walk-Directed-Graph w v)

  vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y) → UU l1
  vertex-on-walk-Directed-Graph w =
    Σ (vertex-Directed-Graph G) (is-vertex-on-walk-Directed-Graph w)

  vertex-vertex-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y) →
    vertex-on-walk-Directed-Graph w → vertex-Directed-Graph G
  vertex-vertex-on-walk-Directed-Graph w = pr1
```

### Edges on a walk

```agda
module _
  {l1 l2 : Level} (G : Directed-Graph l1 l2)
  where

  data is-edge-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G} (w : walk-Directed-Graph G x y)
    {u v : vertex-Directed-Graph G} → edge-Directed-Graph G u v → UU (l1 ⊔ l2)
    where
    edge-is-edge-on-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y)
      (w : walk-Directed-Graph G y z) →
      is-edge-on-walk-Directed-Graph (cons-walk-Directed-Graph e w) e
    cons-is-edge-on-walk-Directed-Graph :
      {x y z : vertex-Directed-Graph G} (e : edge-Directed-Graph G x y)
      (w : walk-Directed-Graph G y z) →
      {u v : vertex-Directed-Graph G} (f : edge-Directed-Graph G u v) →
      is-edge-on-walk-Directed-Graph w f →
      is-edge-on-walk-Directed-Graph (cons-walk-Directed-Graph e w) f

  edge-on-walk-Directed-Graph :
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y) → UU (l1 ⊔ l2)
  edge-on-walk-Directed-Graph w =
    Σ ( total-edge-Directed-Graph G)
      ( λ e →
        is-edge-on-walk-Directed-Graph w (edge-total-edge-Directed-Graph G e))

  module _
    {x y : vertex-Directed-Graph G}
    (w : walk-Directed-Graph G x y)
    (e : edge-on-walk-Directed-Graph w)
    where

    total-edge-edge-on-walk-Directed-Graph : total-edge-Directed-Graph G
    total-edge-edge-on-walk-Directed-Graph = pr1 e
    
    source-edge-on-walk-Directed-Graph : vertex-Directed-Graph G
    source-edge-on-walk-Directed-Graph =
      source-total-edge-Directed-Graph G total-edge-edge-on-walk-Directed-Graph

    target-edge-on-walk-Directed-Graph : vertex-Directed-Graph G
    target-edge-on-walk-Directed-Graph =
      target-total-edge-Directed-Graph G total-edge-edge-on-walk-Directed-Graph

    edge-edge-on-walk-Directed-Graph :
      edge-Directed-Graph G
        source-edge-on-walk-Directed-Graph
        target-edge-on-walk-Directed-Graph
    edge-edge-on-walk-Directed-Graph =
      edge-total-edge-Directed-Graph G total-edge-edge-on-walk-Directed-Graph

    is-edge-on-walk-edge-on-walk-Directed-Graph :
      is-edge-on-walk-Directed-Graph w edge-edge-on-walk-Directed-Graph
    is-edge-on-walk-edge-on-walk-Directed-Graph = pr2 e
```

### The action on walks of graph homomorphisms

```agda
walk-hom-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H) {x y : vertex-Directed-Graph G} →
  walk-Directed-Graph G x y →
  walk-Directed-Graph H
    ( vertex-hom-Directed-Graph G H f x)
    ( vertex-hom-Directed-Graph G H f y)
walk-hom-Directed-Graph G H f refl-walk-Directed-Graph =
  refl-walk-Directed-Graph
walk-hom-Directed-Graph G H f (cons-walk-Directed-Graph e w) =
  cons-walk-Directed-Graph
    ( edge-hom-Directed-Graph G H f e)
    ( walk-hom-Directed-Graph G H f w)
```

### The action on walks of length `n` of graph homomorphisms

```agda
walk-of-length-hom-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : hom-Directed-Graph G H) (n : ℕ) {x y : vertex-Directed-Graph G} →
  walk-of-length-Directed-Graph G n x y →
  walk-of-length-Directed-Graph H n
    ( vertex-hom-Directed-Graph G H f x)
    ( vertex-hom-Directed-Graph G H f y)
walk-of-length-hom-Directed-Graph G H f zero-ℕ {x} {y} (map-raise p) =
  map-raise (ap (vertex-hom-Directed-Graph G H f) p)
walk-of-length-hom-Directed-Graph G H f (succ-ℕ n) {x} {y} (z , e , w) =
  map-Σ
    ( λ z →
      ( edge-Directed-Graph H (vertex-hom-Directed-Graph G H f x) z) ×
      ( walk-of-length-Directed-Graph H n z
        ( vertex-hom-Directed-Graph G H f y)))
    ( vertex-hom-Directed-Graph G H f)
    ( λ z →
      map-prod
        ( edge-hom-Directed-Graph G H f)
        ( walk-of-length-hom-Directed-Graph G H f n))
    ( z , e , w)
```

### The action on walks of length `n` of equivalences of graphs

```agda
equiv-walk-of-length-equiv-hom-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (f : equiv-Directed-Graph G H) (n : ℕ) {x y : vertex-Directed-Graph G} →
  walk-of-length-Directed-Graph G n x y ≃
  walk-of-length-Directed-Graph H n
    ( vertex-equiv-Directed-Graph G H f x)
    ( vertex-equiv-Directed-Graph G H f y)
equiv-walk-of-length-equiv-hom-Directed-Graph G H f zero-ℕ = ?
equiv-walk-of-length-equiv-hom-Directed-Graph G H f (succ-ℕ n) = ?
```

### The action of equivalences on walks

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H)
  where

  walk-equiv-Directed-Graph :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y →
    walk-Directed-Graph H
      ( vertex-equiv-Directed-Graph G H e x)
      ( vertex-equiv-Directed-Graph G H e y)
  walk-equiv-Directed-Graph =
    walk-hom-Directed-Graph G H (hom-equiv-Directed-Graph G H e)

  map-inv-equiv-walk-equiv-Directed-Graph' :
    {x y : vertex-Directed-Graph G} {z : vertex-Directed-Graph H}
    (p : vertex-equiv-Directed-Graph G H e y ＝ z) →
    walk-Directed-Graph H
      ( vertex-equiv-Directed-Graph G H e x)
      ( z) →
    walk-Directed-Graph G x y
  map-inv-equiv-walk-equiv-Directed-Graph' p refl-walk-Directed-Graph =
    {!refl-walk-Directed-Graph!}
  map-inv-equiv-walk-equiv-Directed-Graph' p (cons-walk-Directed-Graph x w) = {!!}

{-
  equiv-walk-equiv-Directed-Graph' :
    {x y : vertex-Directed-Graph G} →
    walk-Directed-Graph G x y ≃
    walk-Directed-Graph H
      ( vertex-equiv-Directed-Graph G H e x)
      ( vertex-equiv-Directed-Graph G H e y)
  equiv-walk-equiv-Directed-Graph' {x} {y} =
    ( ( inv-equiv (compute-walk-Directed-Graph H
        ( map-equiv (pr1 e) x)
        ( map-equiv (pr1 e) y))) ∘e
      ( α)) ∘e
    ( compute-walk-Directed-Graph G x y)
    where
    α = 
      equiv-coprod
      ( equiv-ap (equiv-vertex-equiv-Directed-Graph G H e) y x)
      ( equiv-Σ
        ( λ z →
          ( edge-Directed-Graph H (vertex-equiv-Directed-Graph G H e x) z) ×
          ( walk-Directed-Graph H z (vertex-equiv-Directed-Graph G H e y)))
        ( equiv-vertex-equiv-Directed-Graph G H e)
        ( λ z →
          equiv-prod
            ( equiv-edge-equiv-Directed-Graph G H e x z)
            ( equiv-walk-equiv-Directed-Graph')))
            -}
```
