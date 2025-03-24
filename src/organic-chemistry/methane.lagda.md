# Methane

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module organic-chemistry.methane
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers funext univalence truncations

open import finite-group-theory.tetrahedra-in-3-space funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.empty-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.propositional-truncations funext univalence
open import foundation.unit-type
open import foundation.universe-levels

open import graph-theory.walks-undirected-graphs funext univalence truncations

open import organic-chemistry.alkanes funext univalence truncations
open import organic-chemistry.hydrocarbons funext univalence truncations

open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
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
