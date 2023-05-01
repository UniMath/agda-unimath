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

**Methane** is the simpliest hydrocarbon, and the first alkane.

## Definition

```agda
module _
  (t : tetrahedron-in-3-space)
  where

  methane : hydrocarbon lzero lzero
  methane =
    ( unit-𝔽 , (λ x → empty-𝔽)) ,
    ( λ c → t) ,
    ( λ c → (λ e → ex-falso (pr2 e)) , λ e _ → ex-falso (pr2 e)) ,
    ( λ c x → x) ,
    ( λ c c' →
      concatenate-eq-leq-ℕ
        ( 3)
        ( inv
          ( compute-number-of-elements-is-finite count-empty is-finite-empty))
        ( star)) ,
    ( λ {star star → unit-trunc-Prop refl-walk-Undirected-Graph})

  is-alkane-methane : is-alkane-hydrocarbon methane
  is-alkane-methane c c' e e' = is-prop-empty e e'
```
