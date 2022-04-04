---
title : Voltage graphs
--- 

```agda
{-# OPTIONS --without-K --exact-split #-}

module graph-theory.voltage-graphs where

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import group-theory.groups
```

## Idea

A voltage graph is a directed graph `G` equipped with a group `Π` (the voltage group) and a labelling of the edges of `G` by elements of `Π`.

## Definition

```agda
Voltage-Graph :
  {l1 : Level} (l2 l3 : Level) (Π : Group l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Voltage-Graph l2 l3 Π =
  Σ ( Graph l2 l3)
    ( λ G → {x y : vertex-Graph G} → edge-Graph G x y → type-Group Π)

module _
  {l1 l2 l3 : Level} (Π : Group l1) (G : Voltage-Graph l2 l3 Π)
  where

  graph-Voltage-Graph : Graph l2 l3
  graph-Voltage-Graph = pr1 G

  vertex-Voltage-Graph : UU l2
  vertex-Voltage-Graph = vertex-Graph graph-Voltage-Graph

  edge-Voltage-Graph : (x y : vertex-Voltage-Graph) → UU l3
  edge-Voltage-Graph = edge-Graph graph-Voltage-Graph

  voltage-Voltage-Graph :
    {x y : vertex-Voltage-Graph} → edge-Voltage-Graph x y → type-Group Π
  voltage-Voltage-Graph = pr2 G
```
