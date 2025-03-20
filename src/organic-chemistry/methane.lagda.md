# Methane

```agda
open import foundation.function-extensionality-axiom

module
  organic-chemistry.methane
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers funext

open import finite-group-theory.tetrahedra-in-3-space funext

open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.identity-types funext
open import foundation.propositional-truncations funext
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.walks-undirected-graphs funext

open import organic-chemistry.alkanes funext
open import organic-chemistry.hydrocarbons funext

open import univalent-combinatorics.counting funext
open import univalent-combinatorics.finite-types funext
```

</details>
## Idea

**Methane** is the simplest hydrocarbon, and the first alkane.

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
