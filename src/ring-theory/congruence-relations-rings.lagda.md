# Congruence relations on rings

```agda
module ring-theory.congruence-relations-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids

open import ring-theory.congruence-relations-semirings
open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "congruence relation" Disambiguation="on a ring" Agda=congruence-Ring}}
on a [ring](ring-theory.rings.md) `R` is a
[congruence relation](ring-theory.congruence-relations-semirings.md) on the
underlying [semiring](ring-theory.semirings.md) of `R`.

## Definition

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-congruence-Ring :
    {l2 : Level} → congruence-Ab l2 (ab-Ring R) → UU (l1 ⊔ l2)
  is-congruence-Ring = is-congruence-Semiring (semiring-Ring R)

  is-congruence-equivalence-relation-Ring :
    {l2 : Level} (S : equivalence-relation l2 (type-Ring R)) → UU (l1 ⊔ l2)
  is-congruence-equivalence-relation-Ring S =
    is-congruence-equivalence-relation-Semiring (semiring-Ring R) S

congruence-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
congruence-Ring l2 R = congruence-Semiring l2 (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  congruence-ab-congruence-Ring : congruence-Ab l2 (ab-Ring R)
  congruence-ab-congruence-Ring =
    congruence-additive-monoid-congruence-Semiring (semiring-Ring R) S

  equivalence-relation-congruence-Ring : equivalence-relation l2 (type-Ring R)
  equivalence-relation-congruence-Ring =
    equivalence-relation-congruence-Semiring (semiring-Ring R) S

  prop-congruence-Ring : Relation-Prop l2 (type-Ring R)
  prop-congruence-Ring = prop-congruence-Semiring (semiring-Ring R) S

  sim-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-congruence-Ring = sim-congruence-Semiring (semiring-Ring R) S

  is-prop-sim-congruence-Ring :
    (x y : type-Ring R) → is-prop (sim-congruence-Ring x y)
  is-prop-sim-congruence-Ring =
    is-prop-sim-congruence-Semiring (semiring-Ring R) S

  concatenate-eq-sim-congruence-Ring :
    {x1 x2 y : type-Ring R} →
    x1 ＝ x2 → sim-congruence-Ring x2 y → sim-congruence-Ring x1 y
  concatenate-eq-sim-congruence-Ring refl H = H

  concatenate-sim-eq-congruence-Ring :
    {x y1 y2 : type-Ring R} →
    sim-congruence-Ring x y1 → y1 ＝ y2 → sim-congruence-Ring x y2
  concatenate-sim-eq-congruence-Ring H refl = H

  concatenate-sim-eq-sim-congruence-Ring :
    {x1 x2 y1 y2 : type-Ring R} →
    x1 ＝ x2 → sim-congruence-Ring x2 y1 →
    y1 ＝ y2 → sim-congruence-Ring x1 y2
  concatenate-sim-eq-sim-congruence-Ring refl H refl = H

  refl-congruence-Ring :
    is-reflexive-Relation-Prop prop-congruence-Ring
  refl-congruence-Ring = refl-congruence-Semiring (semiring-Ring R) S

  symmetric-congruence-Ring :
    is-symmetric-Relation-Prop prop-congruence-Ring
  symmetric-congruence-Ring = symmetric-congruence-Semiring (semiring-Ring R) S

  equiv-symmetric-congruence-Ring :
    (x y : type-Ring R) →
    sim-congruence-Ring x y ≃ sim-congruence-Ring y x
  equiv-symmetric-congruence-Ring =
    equiv-symmetric-congruence-Semiring (semiring-Ring R) S

  transitive-congruence-Ring :
    is-transitive-Relation-Prop prop-congruence-Ring
  transitive-congruence-Ring =
    transitive-congruence-Semiring (semiring-Ring R) S

  add-congruence-Ring :
    is-congruence-Ab (ab-Ring R) equivalence-relation-congruence-Ring
  add-congruence-Ring = add-congruence-Semiring (semiring-Ring R) S

  left-add-congruence-Ring :
    (x : type-Ring R) {y z : type-Ring R} →
    sim-congruence-Ring y z →
    sim-congruence-Ring (add-Ring R x y) (add-Ring R x z)
  left-add-congruence-Ring =
    left-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  right-add-congruence-Ring :
    {x y : type-Ring R} → sim-congruence-Ring x y →
    (z : type-Ring R) →
    sim-congruence-Ring (add-Ring R x z) (add-Ring R y z)
  right-add-congruence-Ring =
    right-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  sim-right-subtraction-zero-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-right-subtraction-zero-congruence-Ring =
    sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  map-sim-right-subtraction-zero-congruence-Ring :
    {x y : type-Ring R} → sim-congruence-Ring x y →
    sim-right-subtraction-zero-congruence-Ring x y
  map-sim-right-subtraction-zero-congruence-Ring =
    map-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  map-inv-sim-right-subtraction-zero-congruence-Ring :
    {x y : type-Ring R} →
    sim-right-subtraction-zero-congruence-Ring x y → sim-congruence-Ring x y
  map-inv-sim-right-subtraction-zero-congruence-Ring =
    map-inv-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  sim-left-subtraction-zero-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-left-subtraction-zero-congruence-Ring =
    sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  map-sim-left-subtraction-zero-congruence-Ring :
    {x y : type-Ring R} → sim-congruence-Ring x y →
    sim-left-subtraction-zero-congruence-Ring x y
  map-sim-left-subtraction-zero-congruence-Ring =
    map-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  map-inv-sim-left-subtraction-zero-congruence-Ring :
    {x y : type-Ring R} → sim-left-subtraction-zero-congruence-Ring x y →
    sim-congruence-Ring x y
  map-inv-sim-left-subtraction-zero-congruence-Ring =
    map-inv-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  neg-congruence-Ring :
    {x y : type-Ring R} → sim-congruence-Ring x y →
    sim-congruence-Ring (neg-Ring R x) (neg-Ring R y)
  neg-congruence-Ring =
    neg-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-congruence-Ring)

  mul-congruence-Ring :
    is-congruence-Monoid
      ( multiplicative-monoid-Ring R)
      ( equivalence-relation-congruence-Ring)
  mul-congruence-Ring = pr2 S

  left-mul-congruence-Ring :
    (x : type-Ring R) {y z : type-Ring R} →
    sim-congruence-Ring y z →
    sim-congruence-Ring (mul-Ring R x y) (mul-Ring R x z)
  left-mul-congruence-Ring x H =
    mul-congruence-Ring (refl-congruence-Ring x) H

  right-mul-congruence-Ring :
    {x y : type-Ring R} → sim-congruence-Ring x y →
    (z : type-Ring R) →
    sim-congruence-Ring (mul-Ring R x z) (mul-Ring R y z)
  right-mul-congruence-Ring H z =
    mul-congruence-Ring H (refl-congruence-Ring z)

construct-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) →
  (S : equivalence-relation l2 (type-Ring R)) →
  is-congruence-Ab (ab-Ring R) S →
  is-congruence-Monoid (multiplicative-monoid-Ring R) S →
  congruence-Ring l2 R
pr1 (pr1 (construct-congruence-Ring R S H K)) = S
pr2 (pr1 (construct-congruence-Ring R S H K)) = H
pr2 (construct-congruence-Ring R S H K) = K
```

## Properties

### Characterizing equality of congruence relations of rings

```agda
relate-same-elements-congruence-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) →
  congruence-Ring l2 R → congruence-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Ring R =
  relate-same-elements-congruence-Semiring (semiring-Ring R)

refl-relate-same-elements-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R) →
  relate-same-elements-congruence-Ring R S S
refl-relate-same-elements-congruence-Ring R =
  refl-relate-same-elements-congruence-Semiring (semiring-Ring R)

is-torsorial-relate-same-elements-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R) →
  is-torsorial (relate-same-elements-congruence-Ring R S)
is-torsorial-relate-same-elements-congruence-Ring R =
  is-torsorial-relate-same-elements-congruence-Semiring
    ( semiring-Ring R)

relate-same-elements-eq-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : congruence-Ring l2 R) →
  S ＝ T → relate-same-elements-congruence-Ring R S T
relate-same-elements-eq-congruence-Ring R =
  relate-same-elements-eq-congruence-Semiring (semiring-Ring R)

is-equiv-relate-same-elements-eq-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : congruence-Ring l2 R) →
  is-equiv (relate-same-elements-eq-congruence-Ring R S T)
is-equiv-relate-same-elements-eq-congruence-Ring R =
  is-equiv-relate-same-elements-eq-congruence-Semiring
    ( semiring-Ring R)

extensionality-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : congruence-Ring l2 R) →
  (S ＝ T) ≃ relate-same-elements-congruence-Ring R S T
extensionality-congruence-Ring R =
  extensionality-congruence-Semiring (semiring-Ring R)

eq-relate-same-elements-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : congruence-Ring l2 R) →
  relate-same-elements-congruence-Ring R S T → S ＝ T
eq-relate-same-elements-congruence-Ring R =
  eq-relate-same-elements-congruence-Semiring (semiring-Ring R)
```
