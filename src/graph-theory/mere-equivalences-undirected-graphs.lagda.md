# Mere equivalences of undirected graphs

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.mere-equivalences-undirected-graphs where

open import foundation.propositional-truncations using
  ( trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using
  (UU-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import graph-theory.equivalences-undirected-graphs using
  ( equiv-Undirected-Graph; id-equiv-Undirected-Graph)
open import graph-theory.undirected-graphs using
  ( Undirected-Graph)
```

## Idea

Two unordered graphs are said to be merely equivalent if there merely exists an equivalence of unordered graphs between them.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Undirected-Graph l1 l2) (H : Undirected-Graph l3 l4)
  where

  mere-equiv-Undirected-Graph-Prop : UU-Prop (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-equiv-Undirected-Graph-Prop = trunc-Prop (equiv-Undirected-Graph G H)

  mere-equiv-Undirected-Graph : UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  mere-equiv-Undirected-Graph = type-Prop mere-equiv-Undirected-Graph-Prop

  is-prop-mere-equiv-Undirected-Graph : is-prop mere-equiv-Undirected-Graph
  is-prop-mere-equiv-Undirected-Graph =
    is-prop-type-Prop mere-equiv-Undirected-Graph-Prop
```

## Properties

### The mere equivalence relation on undirected graphs is reflexive

```agda
module _
  {l1 l2 : Level} (G : Undirected-Graph l1 l2)
  where

  refl-mere-equiv-Undirected-Graph : mere-equiv-Undirected-Graph G G
  refl-mere-equiv-Undirected-Graph =
    unit-trunc-Prop (id-equiv-Undirected-Graph G)
```
