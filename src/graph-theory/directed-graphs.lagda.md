# Directed graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.directed-graphs where

open import foundation.universe-levels
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.identity-types
open import foundation.equivalences
```

## Idea

A graph consists of a type of vertices equipped with a binary, type valued relation of edges.

## Definition

```agda
Graph : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Graph l1 l2 = Σ (UU l1) (λ V → V → V → UU l2)

module _
  {l1 l2 : Level} (G : Graph l1 l2)
  where

  vertex-Graph : UU l1
  vertex-Graph = pr1 G

  edge-Graph : vertex-Graph → vertex-Graph → UU l2
  edge-Graph = pr2 G
```

### Alternative definition

```agda
module alternative where

  Graph' : (l1 l2 : Level)  → UU (lsuc l1 ⊔ lsuc l2)
  Graph' l1 l2 = Σ (UU l1)  λ V → Σ (UU l2) (λ E → (E → V) × (E → V))

  module _ {l1 l2 : Level} (G : Graph' l1 l2) where

    vertex-Graph' : UU l1
    vertex-Graph' = pr1 G

    edge-Graph' : UU l2
    edge-Graph' = pr1 (pr2 G)

    source-edge-Graph : edge-Graph' -> vertex-Graph'
    source-edge-Graph = pr1 (pr2 (pr2 G))

    target-edge-Graph : edge-Graph' -> vertex-Graph'
    target-edge-Graph = pr2 (pr2 (pr2 G))
```

```agda
module equiv {l1 l2 : Level} where
  open alternative

  Graph-to-Graph' : Graph l1 l2 -> Graph' l1 (l1 ⊔ l2)
  pr1 (Graph-to-Graph' G) = vertex-Graph G
  pr1 (pr2 (Graph-to-Graph' G))
    = Σ (vertex-Graph G) (λ x → Σ (vertex-Graph G) λ y → edge-Graph G  x y)
  pr1 (pr2 (pr2 (Graph-to-Graph' G))) = pr1
  pr2 (pr2 (pr2 (Graph-to-Graph' G))) = pr1 ∘ pr2

  Graph'-to-Graph : Graph' l1 l2 -> Graph l1 (l1 ⊔ l2)
  Graph'-to-Graph (pair V (pair E (pair st tg)))
    = pair V λ x y → Σ E λ e → (Id (st e) x) × (Id (tg e) y)
```

### Results

#### Equivalence between Graph definitions

The two definitions given above for directed graphs are equivalent. $\Sigma$-types preserve equivalences and a type family $A \to U$ is equivalent to $\sum_{(C : U)} C \to A$.
We use these lemmas in the following calculation:

\begin{equation}
\begin{split}
\sum_{(V\,:\,\mathcal{U})} (V \to V \to \mathcal{U}) & \simeq \sum_{(V\,:\,\mathcal{U})}
 (V \times V \to \mathcal{U}) \\
 &\simeq \sum_{(V,E\,:\,\mathcal{U})} (E \to (V \times V)) \\
&\simeq  \sum_{(V,E\,:\,\mathcal{U})} ((E \to V) \times (E \to V))
\end{split}
\end{equation}


```
module directed-graph-defs-equivalence
  {l1 l2 : Level} where
  -- is-equiv-htpy-equiv
  -- Uses equiv-Fib
  -- universal-property-cartesian-product-types.lagda
  -- equiv.

  -- The canonical (optimal) map for the equivalence.
  -- Any other map is homotopic to the canonical map.
  --is-equi
```

#### The type of Graph forms a category

```agda
-- Show that Graph is pre-category
-- + iso corresponds to equiv.
-- Instance of
```

```
-- TODO
Cyclic graphs
```

#### The type of Graph forms a Topos

```agda
-- Show that Graph is pre-category
-- + iso corresponds to equiv.
-- Instance of
```
