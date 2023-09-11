# Congruence relations on abelian groups

```agda
module group-theory.congruence-relations-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.congruence-relations-groups
```

</details>

## Idea

A congruence relation on an abelian group `A` is a congruence relation on the
underlying group of `A`.

## Definition

```agda
is-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) →
  Equivalence-Relation l2 (type-Ab A) →
  UU (l1 ⊔ l2)
is-congruence-Ab A = is-congruence-Group (group-Ab A)

congruence-Ab : {l : Level} (l2 : Level) (A : Ab l) → UU (l ⊔ lsuc l2)
congruence-Ab l2 A = congruence-Group l2 (group-Ab A)

module _
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A)
  where

  eq-rel-congruence-Ab : Equivalence-Relation l2 (type-Ab A)
  eq-rel-congruence-Ab = eq-rel-congruence-Group (group-Ab A) R

  prop-congruence-Ab : Relation-Prop l2 (type-Ab A)
  prop-congruence-Ab = prop-congruence-Group (group-Ab A) R

  sim-congruence-Ab : (x y : type-Ab A) → UU l2
  sim-congruence-Ab = sim-congruence-Group (group-Ab A) R

  is-prop-sim-congruence-Ab :
    (x y : type-Ab A) → is-prop (sim-congruence-Ab x y)
  is-prop-sim-congruence-Ab =
    is-prop-sim-congruence-Group (group-Ab A) R

  concatenate-eq-sim-congruence-Ab :
    {x1 x2 y : type-Ab A} →
    x1 ＝ x2 → sim-congruence-Ab x2 y → sim-congruence-Ab x1 y
  concatenate-eq-sim-congruence-Ab =
    concatenate-eq-sim-congruence-Group (group-Ab A) R

  concatenate-sim-eq-congruence-Ab :
    {x y1 y2 : type-Ab A} →
    sim-congruence-Ab x y1 → y1 ＝ y2 → sim-congruence-Ab x y2
  concatenate-sim-eq-congruence-Ab =
    concatenate-sim-eq-congruence-Group (group-Ab A) R

  concatenate-eq-sim-eq-congruence-Ab :
    {x1 x2 y1 y2 : type-Ab A} → x1 ＝ x2 →
    sim-congruence-Ab x2 y1 →
    y1 ＝ y2 → sim-congruence-Ab x1 y2
  concatenate-eq-sim-eq-congruence-Ab =
    concatenate-eq-sim-eq-congruence-Group (group-Ab A) R

  refl-congruence-Ab : is-reflexive sim-congruence-Ab
  refl-congruence-Ab = refl-congruence-Group (group-Ab A) R

  symmetric-congruence-Ab : is-symmetric sim-congruence-Ab
  symmetric-congruence-Ab = symmetric-congruence-Group (group-Ab A) R

  equiv-symmetric-congruence-Ab :
    (x y : type-Ab A) →
    sim-congruence-Ab x y ≃ sim-congruence-Ab y x
  equiv-symmetric-congruence-Ab =
    equiv-symmetric-congruence-Group (group-Ab A) R

  transitive-congruence-Ab :
    is-transitive sim-congruence-Ab
  transitive-congruence-Ab = transitive-congruence-Group (group-Ab A) R

  add-congruence-Ab : is-congruence-Ab A eq-rel-congruence-Ab
  add-congruence-Ab = mul-congruence-Group (group-Ab A) R

  left-add-congruence-Ab :
    (x : type-Ab A) {y z : type-Ab A} →
    sim-congruence-Ab y z →
    sim-congruence-Ab (add-Ab A x y) (add-Ab A x z)
  left-add-congruence-Ab = left-mul-congruence-Group (group-Ab A) R

  right-add-congruence-Ab :
    {x y : type-Ab A} → sim-congruence-Ab x y →
    (z : type-Ab A) →
    sim-congruence-Ab (add-Ab A x z) (add-Ab A y z)
  right-add-congruence-Ab = right-mul-congruence-Group (group-Ab A) R

  conjugation-congruence-Ab :
    (x : type-Ab A) {y z : type-Ab A} → sim-congruence-Ab y z →
    sim-congruence-Ab (conjugation-Ab A x y) (conjugation-Ab A x z)
  conjugation-congruence-Ab =
    conjugation-congruence-Group (group-Ab A) R

  conjugation-congruence-Ab' :
    (x : type-Ab A) {y z : type-Ab A} →
    sim-congruence-Ab y z →
    sim-congruence-Ab
      ( conjugation-Ab' A x y)
      ( conjugation-Ab' A x z)
  conjugation-congruence-Ab' =
    conjugation-congruence-Group' (group-Ab A) R

  sim-right-subtraction-zero-congruence-Ab : (x y : type-Ab A) → UU l2
  sim-right-subtraction-zero-congruence-Ab =
    sim-right-div-unit-congruence-Group (group-Ab A) R

  map-sim-right-subtraction-zero-congruence-Ab :
    {x y : type-Ab A} → sim-congruence-Ab x y →
    sim-right-subtraction-zero-congruence-Ab x y
  map-sim-right-subtraction-zero-congruence-Ab =
    map-sim-right-div-unit-congruence-Group (group-Ab A) R

  map-inv-sim-right-subtraction-zero-congruence-Ab :
    {x y : type-Ab A} →
    sim-right-subtraction-zero-congruence-Ab x y → sim-congruence-Ab x y
  map-inv-sim-right-subtraction-zero-congruence-Ab =
    map-inv-sim-right-div-unit-congruence-Group (group-Ab A) R

  sim-left-subtraction-zero-congruence-Ab : (x y : type-Ab A) → UU l2
  sim-left-subtraction-zero-congruence-Ab =
    sim-left-div-unit-congruence-Group (group-Ab A) R

  map-sim-left-subtraction-zero-congruence-Ab :
    {x y : type-Ab A} → sim-congruence-Ab x y →
    sim-left-subtraction-zero-congruence-Ab x y
  map-sim-left-subtraction-zero-congruence-Ab =
    map-sim-left-div-unit-congruence-Group (group-Ab A) R

  map-inv-sim-left-subtraction-zero-congruence-Ab :
    {x y : type-Ab A} → sim-left-subtraction-zero-congruence-Ab x y →
    sim-congruence-Ab x y
  map-inv-sim-left-subtraction-zero-congruence-Ab =
    map-inv-sim-left-div-unit-congruence-Group (group-Ab A) R

  neg-congruence-Ab :
    {x y : type-Ab A} → sim-congruence-Ab x y →
    sim-congruence-Ab (neg-Ab A x) (neg-Ab A y)
  neg-congruence-Ab = inv-congruence-Group (group-Ab A) R
```

## Properties

### Characterizing equality of congruence relations on groups

```agda
relate-same-elements-congruence-Ab :
  {l1 l2 l3 : Level} (A : Ab l1) →
  congruence-Ab l2 A → congruence-Ab l3 A → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Ab A =
  relate-same-elements-congruence-Group (group-Ab A)

refl-relate-same-elements-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A) →
  relate-same-elements-congruence-Ab A R R
refl-relate-same-elements-congruence-Ab A =
  refl-relate-same-elements-congruence-Group (group-Ab A)

is-contr-total-relate-same-elements-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R : congruence-Ab l2 A) →
  is-contr
    ( Σ ( congruence-Ab l2 A)
        ( relate-same-elements-congruence-Ab A R))
is-contr-total-relate-same-elements-congruence-Ab A =
  is-contr-total-relate-same-elements-congruence-Group (group-Ab A)

relate-same-elements-eq-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R S : congruence-Ab l2 A) →
  R ＝ S → relate-same-elements-congruence-Ab A R S
relate-same-elements-eq-congruence-Ab A =
  relate-same-elements-eq-congruence-Group (group-Ab A)

is-equiv-relate-same-elements-eq-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R S : congruence-Ab l2 A) →
  is-equiv (relate-same-elements-eq-congruence-Ab A R S)
is-equiv-relate-same-elements-eq-congruence-Ab A =
  is-equiv-relate-same-elements-eq-congruence-Group (group-Ab A)

extensionality-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R S : congruence-Ab l2 A) →
  (R ＝ S) ≃ relate-same-elements-congruence-Ab A R S
extensionality-congruence-Ab A =
  extensionality-congruence-Group (group-Ab A)

eq-relate-same-elements-congruence-Ab :
  {l1 l2 : Level} (A : Ab l1) (R S : congruence-Ab l2 A) →
  relate-same-elements-congruence-Ab A R S → R ＝ S
eq-relate-same-elements-congruence-Ab A =
  eq-relate-same-elements-congruence-Group (group-Ab A)
```
