# Equivalences of directed graphs

```agda
module graph-theory.equivalences-directed-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.morphisms-directed-graphs
```

</details>

## Definition

### The type of equivalences of directed graphs

```agda
equiv-Directed-Graph :
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
equiv-Directed-Graph G H =
  Σ ( vertex-Directed-Graph G ≃ vertex-Directed-Graph H)
    ( λ e →
      (x y : vertex-Directed-Graph G) →
      edge-Directed-Graph G x y ≃
      edge-Directed-Graph H (map-equiv e x) (map-equiv e y))

module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  (e : equiv-Directed-Graph G H)
  where

  equiv-vertex-equiv-Directed-Graph :
    vertex-Directed-Graph G ≃ vertex-Directed-Graph H
  equiv-vertex-equiv-Directed-Graph = pr1 e

  vertex-equiv-Directed-Graph :
    vertex-Directed-Graph G → vertex-Directed-Graph H
  vertex-equiv-Directed-Graph = map-equiv equiv-vertex-equiv-Directed-Graph

  inv-vertex-equiv-Directed-Graph :
    vertex-Directed-Graph H → vertex-Directed-Graph G
  inv-vertex-equiv-Directed-Graph =
    map-inv-equiv equiv-vertex-equiv-Directed-Graph

  issec-inv-vertex-equiv-Directed-Graph :
    ( vertex-equiv-Directed-Graph ∘ inv-vertex-equiv-Directed-Graph) ~ id
  issec-inv-vertex-equiv-Directed-Graph =
    issec-map-inv-equiv equiv-vertex-equiv-Directed-Graph

  isretr-inv-vertex-equiv-Directed-Graph :
    ( inv-vertex-equiv-Directed-Graph ∘ vertex-equiv-Directed-Graph) ~ id
  isretr-inv-vertex-equiv-Directed-Graph =
    isretr-map-inv-equiv equiv-vertex-equiv-Directed-Graph

  equiv-edge-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y ≃
    edge-Directed-Graph H
      ( vertex-equiv-Directed-Graph x)
      ( vertex-equiv-Directed-Graph y)
  equiv-edge-equiv-Directed-Graph = pr2 e

  edge-equiv-Directed-Graph :
    (x y : vertex-Directed-Graph G) →
    edge-Directed-Graph G x y →
    edge-Directed-Graph H
      ( vertex-equiv-Directed-Graph x)
      ( vertex-equiv-Directed-Graph y)
  edge-equiv-Directed-Graph x y =
    map-equiv (equiv-edge-equiv-Directed-Graph x y)
```

### The condition on a morphism of directed graphs to be an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Directed-Graph l1 l2) (H : Directed-Graph l3 l4)
  where

  is-equiv-hom-Directed-Graph :
    hom-Directed-Graph G H → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-hom-Directed-Graph f =
    ( is-equiv (vertex-hom-Directed-Graph G H f)) ×
    ( (x y : vertex-Directed-Graph G) →
      is-equiv (edge-hom-Directed-Graph G H f {x} {y}))

  compute-equiv-Directed-Graph :
    equiv-Directed-Graph G H ≃
    Σ (hom-Directed-Graph G H) is-equiv-hom-Directed-Graph
  compute-equiv-Directed-Graph =
    interchange-Σ-Σ
      ( λ fV H fE → (x y : vertex-Directed-Graph G) → is-equiv (fE x y)) ∘e
      ( equiv-tot
        ( λ fV → distributive-Π-Σ ∘e equiv-map-Π (λ x → distributive-Π-Σ)))

  hom-equiv-Directed-Graph :
    equiv-Directed-Graph G H → hom-Directed-Graph G H
  hom-equiv-Directed-Graph e =
    pr1 (map-equiv compute-equiv-Directed-Graph e)

  compute-hom-equiv-Directed-Graph :
    (e : equiv-Directed-Graph G H) →
    hom-equiv-Directed-Graph e ＝
    ( vertex-equiv-Directed-Graph G H e , edge-equiv-Directed-Graph G H e)
  compute-hom-equiv-Directed-Graph e = refl

  is-equiv-equiv-Directed-Graph :
    (e : equiv-Directed-Graph G H) →
    is-equiv-hom-Directed-Graph (hom-equiv-Directed-Graph e)
  is-equiv-equiv-Directed-Graph e =
    pr2 (map-equiv compute-equiv-Directed-Graph e)
```

## Properties
