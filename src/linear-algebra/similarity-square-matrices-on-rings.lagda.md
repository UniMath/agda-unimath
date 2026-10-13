# Similarity of square matrices on rings

```agda
module linear-algebra.similarity-square-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.universe-levels

open import group-theory.conjugation-invertible-elements-monoids

open import linear-algebra.multiplication-square-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
```

</details>

## Idea

Two `n × n` [square matrices](linear-algebra.square-matrices-on-rings.md) `M`
and `N` on a [ring](ring-theory.rings.md) are
{{#concept "similar" WDID=Q254491 WD="matrix similarity" Disambiguation="square matrices on a ring" Agda=sim-square-matrix-Ring}}
if there [exists](foundation.existential-quantification.md) an
[invertible matrix](linear-algebra.invertible-matrices-on-rings.md) `P` such
that `N = P⁻¹MP`.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  equivalence-relation-sim-square-matrix-Ring :
    equivalence-relation l (square-matrix-Ring R n)
  equivalence-relation-sim-square-matrix-Ring =
    equivalence-relation-is-conjugate-invertible-element-Monoid
      ( monoid-mul-square-matrix-Ring R n)

  sim-square-matrix-Ring :
    Relation l (square-matrix-Ring R n)
  sim-square-matrix-Ring =
    sim-equivalence-relation equivalence-relation-sim-square-matrix-Ring

  sim-prop-square-matrix-Ring :
    Relation-Prop l (square-matrix-Ring R n)
  sim-prop-square-matrix-Ring =
    prop-equivalence-relation equivalence-relation-sim-square-matrix-Ring

  refl-sim-square-matrix-Ring :
    is-reflexive sim-square-matrix-Ring
  refl-sim-square-matrix-Ring =
    refl-equivalence-relation equivalence-relation-sim-square-matrix-Ring

  symmetric-sim-square-matrix-Ring :
    is-symmetric sim-square-matrix-Ring
  symmetric-sim-square-matrix-Ring =
    symmetric-equivalence-relation equivalence-relation-sim-square-matrix-Ring

  transitive-sim-square-matrix-Ring :
    is-transitive sim-square-matrix-Ring
  transitive-sim-square-matrix-Ring =
    transitive-equivalence-relation equivalence-relation-sim-square-matrix-Ring
```
