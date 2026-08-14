# Left congruence relations on rings

```agda
module ring-theory.left-congruence-relations-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids

open import ring-theory.left-congruence-relations-semirings
open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "left congruence relation" Disambiguation="on a ring" WD="congruence relation" WDID=Q8349849 Agda=left-congruence-Ring}}
on a [ring](ring-theory.rings.md) `R` is a
[left congruence relation](ring-theory.left-congruence-relations-semirings.md) on the
underlying [semiring](ring-theory.semirings.md) of `R`. Left congruence relations on a ring `R` correspond to kernels of morphisms `R → M` into a left `R`-module.

## Definitions

### The type of left congruence relations on the underlying additive monoid of a ring

```agda
module _
  {l1 : Level} (l2 : Level) (R : Ring l1)
  where

  congruence-additive-monoid-Ring :
    UU (l1 ⊔ lsuc l2)
  congruence-additive-monoid-Ring =
    congruence-additive-monoid-Semiring l2 (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1)
  (S : congruence-additive-monoid-Ring l2 R)
  where

  sim-congruence-additive-monoid-Ring :
    (x y : type-Ring R) → UU l2
  sim-congruence-additive-monoid-Ring =
    sim-congruence-additive-monoid-Semiring (semiring-Ring R) S

  is-prop-sim-congruence-additive-monoid-Ring :
    (x y : type-Ring R) →
    is-prop (sim-congruence-additive-monoid-Ring x y)
  is-prop-sim-congruence-additive-monoid-Ring =
    is-prop-sim-congruence-additive-monoid-Semiring (semiring-Ring R) S

  sim-prop-congruence-additive-monoid-Ring :
    (x y : type-Ring R) → Prop l2
  sim-prop-congruence-additive-monoid-Ring =
    sim-prop-congruence-additive-monoid-Semiring (semiring-Ring R) S
```

### The predicate of being a left congruence relation

```agda
module _
  {l1 l2 : Level} (R : Ring l1)
  (S : congruence-Monoid l2 (additive-monoid-Ring R))
  where

  is-left-congruence-congruence-additive-monoid-Ring :
    UU (l1 ⊔ l2)
  is-left-congruence-congruence-additive-monoid-Ring =
    is-left-congruence-congruence-additive-monoid-Semiring (semiring-Ring R) S

  is-prop-is-left-congruence-congruence-additive-monoid-Ring :
    is-prop is-left-congruence-congruence-additive-monoid-Ring
  is-prop-is-left-congruence-congruence-additive-monoid-Ring =
    is-prop-is-left-congruence-congruence-additive-monoid-Semiring
      ( semiring-Ring R)
      ( S)

  is-left-congruence-prop-congruence-additive-monoid-Ring :
    Prop (l1 ⊔ l2)
  is-left-congruence-prop-congruence-additive-monoid-Ring =
    is-left-congruence-prop-congruence-additive-monoid-Semiring (semiring-Ring R) S

module _
  {l1 l2 : Level} (R : Ring l1)
  (S : equivalence-relation l2 (type-Ring R))
  where

  is-left-congruence-equivalence-relation-Ring :
    UU (l1 ⊔ l2)
  is-left-congruence-equivalence-relation-Ring =
    is-left-congruence-equivalence-relation-Semiring (semiring-Ring R) S

  is-prop-is-left-congruence-equivalence-relation-Ring :
    is-prop is-left-congruence-equivalence-relation-Ring
  is-prop-is-left-congruence-equivalence-relation-Ring =
    is-prop-is-left-congruence-equivalence-relation-Semiring (semiring-Ring R) S

  is-left-congruence-prop-equivalence-relation-Ring :
    Prop (l1 ⊔ l2)
  is-left-congruence-prop-equivalence-relation-Ring =
    is-left-congruence-prop-equivalence-relation-Semiring (semiring-Ring R) S

left-congruence-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
left-congruence-Ring l2 R =
  left-congruence-Semiring l2 (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : left-congruence-Ring l2 R)
  where

  congruence-additive-monoid-left-congruence-Ring :
    congruence-Monoid l2 (additive-monoid-Ring R)
  congruence-additive-monoid-left-congruence-Ring =
    congruence-additive-monoid-left-congruence-Semiring (semiring-Ring R) S

  is-left-congruence-left-congruence-Ring :
    is-left-congruence-congruence-additive-monoid-Ring R
      congruence-additive-monoid-left-congruence-Ring
  is-left-congruence-left-congruence-Ring =
    is-left-congruence-left-congruence-Semiring (semiring-Ring R) S

  equivalence-relation-left-congruence-Ring :
    equivalence-relation l2 (type-Ring R)
  equivalence-relation-left-congruence-Ring =
    equivalence-relation-left-congruence-Semiring (semiring-Ring R) S

  sim-left-congruence-Ring :
    (x y : type-Ring R) → UU l2
  sim-left-congruence-Ring =
    sim-left-congruence-Semiring (semiring-Ring R) S

  is-prop-sim-left-congruence-Ring :
    (x y : type-Ring R) → is-prop (sim-left-congruence-Ring x y)
  is-prop-sim-left-congruence-Ring =
    is-prop-sim-left-congruence-Semiring (semiring-Ring R) S

  sim-prop-left-congruence-Ring :
    (x y : type-Ring R) → Prop l2
  sim-prop-left-congruence-Ring =
    sim-prop-left-congruence-Semiring (semiring-Ring R) S

  refl-left-congruence-Ring :
    is-reflexive sim-left-congruence-Ring
  refl-left-congruence-Ring =
    refl-left-congruence-Semiring (semiring-Ring R) S

  symmetric-left-congruence-Ring :
    is-symmetric sim-left-congruence-Ring
  symmetric-left-congruence-Ring =
    symmetric-left-congruence-Semiring (semiring-Ring R) S

  equiv-symmetric-left-congruence-Ring :
    (x y : type-Ring R) →
    sim-left-congruence-Ring x y ≃ sim-left-congruence-Ring y x
  equiv-symmetric-left-congruence-Ring =
    equiv-symmetric-left-congruence-Semiring (semiring-Ring R) S

  transitive-left-congruence-Ring :
    is-transitive sim-left-congruence-Ring
  transitive-left-congruence-Ring =
    transitive-left-congruence-Semiring (semiring-Ring R) S

  concatenate-eq-sim-left-congruence-Ring :
    {x1 x2 y : type-Ring R} →
    x1 ＝ x2 → sim-left-congruence-Ring x2 y → sim-left-congruence-Ring x1 y
  concatenate-eq-sim-left-congruence-Ring =
    concatenate-eq-sim-left-congruence-Semiring (semiring-Ring R) S

  concatenate-sim-eq-left-congruence-Ring :
    {x y1 y2 : type-Ring R} →
    sim-left-congruence-Ring x y1 → y1 ＝ y2 → sim-left-congruence-Ring x y2
  concatenate-sim-eq-left-congruence-Ring =
    concatenate-sim-eq-left-congruence-Semiring (semiring-Ring R) S

  concatenate-eq-sim-eq-left-congruence-Ring :
    {x1 x2 y1 y2 : type-Ring R} →
    x1 ＝ x2 → sim-left-congruence-Ring x2 y1 →
    y1 ＝ y2 → sim-left-congruence-Ring x1 y2
  concatenate-eq-sim-eq-left-congruence-Ring =
    concatenate-eq-sim-eq-left-congruence-Semiring (semiring-Ring R) S

  is-additive-congruence-left-congruence-Ring :
    is-congruence-Monoid
      ( additive-monoid-Ring R)
      ( equivalence-relation-left-congruence-Ring)
  is-additive-congruence-left-congruence-Ring =
    is-additive-congruence-left-congruence-Semiring (semiring-Ring R) S

  congruence-ab-left-congruence-Ring : congruence-Ab l2 (ab-Ring R)
  pr1 congruence-ab-left-congruence-Ring =
    equivalence-relation-left-congruence-Ring
  pr2 congruence-ab-left-congruence-Ring =
    is-additive-congruence-left-congruence-Ring

  add-left-congruence-Ring :
    {x y u v : type-Ring R} →
    sim-left-congruence-Ring x y → sim-left-congruence-Ring u v →
    sim-left-congruence-Ring (add-Ring R x u) (add-Ring R y v)
  add-left-congruence-Ring =
    is-additive-congruence-left-congruence-Ring

  left-add-left-congruence-Ring :
    (x : type-Ring R) {y z : type-Ring R} →
    sim-left-congruence-Ring y z →
    sim-left-congruence-Ring (add-Ring R x y) (add-Ring R x z)
  left-add-left-congruence-Ring =
    left-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  right-add-left-congruence-Ring :
    {x y : type-Ring R} → sim-left-congruence-Ring x y →
    (z : type-Ring R) →
    sim-left-congruence-Ring (add-Ring R x z) (add-Ring R y z)
  right-add-left-congruence-Ring =
    right-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  sim-right-subtraction-zero-left-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-right-subtraction-zero-left-congruence-Ring =
    sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  map-sim-right-subtraction-zero-left-congruence-Ring :
    {x y : type-Ring R} → sim-left-congruence-Ring x y →
    sim-right-subtraction-zero-left-congruence-Ring x y
  map-sim-right-subtraction-zero-left-congruence-Ring =
    map-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  map-inv-sim-right-subtraction-zero-left-congruence-Ring :
    {x y : type-Ring R} →
    sim-right-subtraction-zero-left-congruence-Ring x y → sim-left-congruence-Ring x y
  map-inv-sim-right-subtraction-zero-left-congruence-Ring =
    map-inv-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  sim-left-subtraction-zero-left-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-left-subtraction-zero-left-congruence-Ring =
    sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  map-sim-left-subtraction-zero-left-congruence-Ring :
    {x y : type-Ring R} → sim-left-congruence-Ring x y →
    sim-left-subtraction-zero-left-congruence-Ring x y
  map-sim-left-subtraction-zero-left-congruence-Ring =
    map-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  map-inv-sim-left-subtraction-zero-left-congruence-Ring :
    {x y : type-Ring R} → sim-left-subtraction-zero-left-congruence-Ring x y →
    sim-left-congruence-Ring x y
  map-inv-sim-left-subtraction-zero-left-congruence-Ring =
    map-inv-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  neg-left-congruence-Ring :
    {x y : type-Ring R} → sim-left-congruence-Ring x y →
    sim-left-congruence-Ring (neg-Ring R x) (neg-Ring R y)
  neg-left-congruence-Ring =
    neg-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-left-congruence-Ring)

  left-mul-left-congruence-Ring :
    (x : type-Ring R) {y z : type-Ring R} →
    sim-left-congruence-Ring y z →
    sim-left-congruence-Ring (mul-Ring R x y) (mul-Ring R x z)
  left-mul-left-congruence-Ring x H =
    is-left-congruence-left-congruence-Ring H
```

## Properties

### Characterizing equality of left congruence relations of rings

```agda
relate-same-elements-left-congruence-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) →
  left-congruence-Ring l2 R → left-congruence-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-left-congruence-Ring R =
  relate-same-elements-left-congruence-Semiring (semiring-Ring R)

refl-relate-same-elements-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : left-congruence-Ring l2 R) →
  relate-same-elements-left-congruence-Ring R S S
refl-relate-same-elements-left-congruence-Ring R =
  refl-relate-same-elements-left-congruence-Semiring (semiring-Ring R)

is-torsorial-relate-same-elements-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : left-congruence-Ring l2 R) →
  is-torsorial (relate-same-elements-left-congruence-Ring R S)
is-torsorial-relate-same-elements-left-congruence-Ring R =
  is-torsorial-relate-same-elements-left-congruence-Semiring
    ( semiring-Ring R)

relate-same-elements-eq-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : left-congruence-Ring l2 R) →
  S ＝ T → relate-same-elements-left-congruence-Ring R S T
relate-same-elements-eq-left-congruence-Ring R =
  relate-same-elements-eq-left-congruence-Semiring (semiring-Ring R)

is-equiv-relate-same-elements-eq-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : left-congruence-Ring l2 R) →
  is-equiv (relate-same-elements-eq-left-congruence-Ring R S T)
is-equiv-relate-same-elements-eq-left-congruence-Ring R =
  is-equiv-relate-same-elements-eq-left-congruence-Semiring
    ( semiring-Ring R)

extensionality-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : left-congruence-Ring l2 R) →
  (S ＝ T) ≃ relate-same-elements-left-congruence-Ring R S T
extensionality-left-congruence-Ring R =
  extensionality-left-congruence-Semiring (semiring-Ring R)

eq-relate-same-elements-left-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : left-congruence-Ring l2 R) →
  relate-same-elements-left-congruence-Ring R S T → S ＝ T
eq-relate-same-elements-left-congruence-Ring R =
  eq-relate-same-elements-left-congruence-Semiring (semiring-Ring R)
```
