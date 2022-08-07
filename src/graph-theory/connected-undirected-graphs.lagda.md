# Connected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.connected-undirected-graphs where

open import foundation.propositional-truncations using (type-trunc-Prop; is-prop-type-trunc-Prop)
open import foundation.propositions using
  ( is-prop; is-prop-Π )
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import graph-theory.undirected-graphs using
  ( Undirected-Graph; vertex-Undirected-Graph)
open import graph-theory.walks-undirected-graphs using
  ( walk-Undirected-Graph)
```

## Idea

A graph is said to be connected if any point can be reached from any point by a walk.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  is-connected-Undirected-Graph : UU (l1 ⊔ l2 ⊔ lsuc lzero)
  is-connected-Undirected-Graph =
    (x y : vertex-Undirected-Graph G) →
    type-trunc-Prop (walk-Undirected-Graph G x y)
```

## Properties

### The property of being connected for an undirected graph is a proposition

```agda
  is-prop-is-connected-Undirected-Graph
    : is-prop is-connected-Undirected-Graph
  is-prop-is-connected-Undirected-Graph =
     is-prop-Π (λ _ → is-prop-Π (λ _ → is-prop-type-trunc-Prop))
```
