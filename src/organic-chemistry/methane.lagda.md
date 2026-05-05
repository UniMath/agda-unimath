# Methane

```agda
module organic-chemistry.methane where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers

open import finite-group-theory.tetrahedra-in-3-space

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.walks-undirected-graphs

open import organic-chemistry.alkanes
open import organic-chemistry.hydrocarbons

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>
## Idea

{{#concept "Methane" WD="methane" WDID=Q37129 Agda=methane}} is the simplest
[hydrocarbon](organic-chemistry.hydrocarbons.md), and the first
[alkane](organic-chemistry.alkanes.md).

## Definition

```agda
module _
  (t : tetrahedron-in-3-space)
  where

  methane : hydrocarbon lzero lzero
  pr1 (pr1 methane) = unit-Finite-Type
  pr2 (pr1 methane) x = empty-Finite-Type
  pr1 (pr2 methane) c = t
  pr1 (pr1 (pr2 (pr2 methane)) c) e = ex-falso (pr2 e)
  pr2 (pr1 (pr2 (pr2 methane)) c) e = ex-falso (pr2 e)
  pr1 (pr2 (pr2 (pr2 methane))) c x = x
  pr1 (pr2 (pr2 (pr2 (pr2 methane)))) c c' =
    concatenate-eq-leq-ℕ
      ( 3)
      ( inv (compute-number-of-elements-is-finite count-empty is-finite-empty))
      ( star)
  pr2 (pr2 (pr2 (pr2 (pr2 methane)))) star star =
    unit-trunc-Prop refl-walk-Undirected-Graph

  is-alkane-methane : is-alkane-hydrocarbon methane
  is-alkane-methane c c' e e' = is-prop-empty e e'
```
