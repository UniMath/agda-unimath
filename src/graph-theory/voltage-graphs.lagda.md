# Voltage graphs

```agda
module graph-theory.voltage-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import graph-theory.directed-graphs

open import group-theory.groups
```

</details>

## Idea

A voltage graph is a directed graph `G` equipped with a group `Π` (the voltage
group) and a labelling of the edges of `G` by elements of `Π`.

## Definition

```agda
Voltage-Graph :
  {l1 : Level} (l2 l3 : Level) (Π : Group l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
Voltage-Graph l2 l3 Π =
  Σ ( Directed-Graph l2 l3)
    ( λ G →
      {x y : vertex-Directed-Graph G} →
      edge-Directed-Graph G x y → type-Group Π)

module _
  {l1 l2 l3 : Level} (Π : Group l1) (G : Voltage-Graph l2 l3 Π)
  where

  graph-Voltage-Graph : Directed-Graph l2 l3
  graph-Voltage-Graph = pr1 G

  vertex-Voltage-Graph : UU l2
  vertex-Voltage-Graph = vertex-Directed-Graph graph-Voltage-Graph

  edge-Voltage-Graph : (x y : vertex-Voltage-Graph) → UU l3
  edge-Voltage-Graph = edge-Directed-Graph graph-Voltage-Graph

  voltage-Voltage-Graph :
    {x y : vertex-Voltage-Graph} → edge-Voltage-Graph x y → type-Group Π
  voltage-Voltage-Graph = pr2 G
```
