# Right congruence relations on rings

```agda
module ring-theory.right-congruence-relations-rings where
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

open import ring-theory.right-congruence-relations-semirings
open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "right congruence relation" Disambiguation="on a ring" WD="congruence relation" WDID=Q8349849 Agda=right-congruence-Ring}}
on a [ring](ring-theory.rings.md) `R` is a
[right congruence relation](ring-theory.right-congruence-relations-semirings.md) on the
underlying [semiring](ring-theory.semirings.md) of `R`.

## Definitions

### The type of right congruence relations on the underlying additive monoid of a ring

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

### The predicate of being a right congruence relation

```agda
module _
  {l1 l2 : Level} (R : Ring l1)
  (S : congruence-Monoid l2 (additive-monoid-Ring R))
  where

  is-right-congruence-congruence-additive-monoid-Ring :
    UU (l1 ⊔ l2)
  is-right-congruence-congruence-additive-monoid-Ring =
    is-right-congruence-congruence-additive-monoid-Semiring (semiring-Ring R) S

  is-prop-is-right-congruence-congruence-additive-monoid-Ring :
    is-prop is-right-congruence-congruence-additive-monoid-Ring
  is-prop-is-right-congruence-congruence-additive-monoid-Ring =
    is-prop-is-right-congruence-congruence-additive-monoid-Semiring
      ( semiring-Ring R)
      ( S)

  is-right-congruence-prop-congruence-additive-monoid-Ring :
    Prop (l1 ⊔ l2)
  is-right-congruence-prop-congruence-additive-monoid-Ring =
    is-right-congruence-prop-congruence-additive-monoid-Semiring (semiring-Ring R) S

module _
  {l1 l2 : Level} (R : Ring l1)
  (S : equivalence-relation l2 (type-Ring R))
  where

  is-right-congruence-equivalence-relation-Ring :
    UU (l1 ⊔ l2)
  is-right-congruence-equivalence-relation-Ring =
    is-right-congruence-equivalence-relation-Semiring (semiring-Ring R) S

  is-prop-is-right-congruence-equivalence-relation-Ring :
    is-prop is-right-congruence-equivalence-relation-Ring
  is-prop-is-right-congruence-equivalence-relation-Ring =
    is-prop-is-right-congruence-equivalence-relation-Semiring (semiring-Ring R) S

  is-right-congruence-prop-equivalence-relation-Ring :
    Prop (l1 ⊔ l2)
  is-right-congruence-prop-equivalence-relation-Ring =
    is-right-congruence-prop-equivalence-relation-Semiring (semiring-Ring R) S

right-congruence-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
right-congruence-Ring l2 R =
  right-congruence-Semiring l2 (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : right-congruence-Ring l2 R)
  where

  congruence-additive-monoid-right-congruence-Ring :
    congruence-Monoid l2 (additive-monoid-Ring R)
  congruence-additive-monoid-right-congruence-Ring =
    congruence-additive-monoid-right-congruence-Semiring (semiring-Ring R) S

  is-right-congruence-right-congruence-Ring :
    is-right-congruence-congruence-additive-monoid-Ring R
      congruence-additive-monoid-right-congruence-Ring
  is-right-congruence-right-congruence-Ring =
    is-right-congruence-right-congruence-Semiring (semiring-Ring R) S

  equivalence-relation-right-congruence-Ring :
    equivalence-relation l2 (type-Ring R)
  equivalence-relation-right-congruence-Ring =
    equivalence-relation-right-congruence-Semiring (semiring-Ring R) S

  sim-right-congruence-Ring :
    (x y : type-Ring R) → UU l2
  sim-right-congruence-Ring =
    sim-right-congruence-Semiring (semiring-Ring R) S

  is-prop-sim-right-congruence-Ring :
    (x y : type-Ring R) → is-prop (sim-right-congruence-Ring x y)
  is-prop-sim-right-congruence-Ring =
    is-prop-sim-right-congruence-Semiring (semiring-Ring R) S

  sim-prop-right-congruence-Ring :
    (x y : type-Ring R) → Prop l2
  sim-prop-right-congruence-Ring =
    sim-prop-right-congruence-Semiring (semiring-Ring R) S

  refl-right-congruence-Ring :
    is-reflexive sim-right-congruence-Ring
  refl-right-congruence-Ring =
    refl-right-congruence-Semiring (semiring-Ring R) S

  symmetric-right-congruence-Ring :
    is-symmetric sim-right-congruence-Ring
  symmetric-right-congruence-Ring =
    symmetric-right-congruence-Semiring (semiring-Ring R) S

  equiv-symmetric-right-congruence-Ring :
    (x y : type-Ring R) →
    sim-right-congruence-Ring x y ≃ sim-right-congruence-Ring y x
  equiv-symmetric-right-congruence-Ring =
    equiv-symmetric-right-congruence-Semiring (semiring-Ring R) S

  transitive-right-congruence-Ring :
    is-transitive sim-right-congruence-Ring
  transitive-right-congruence-Ring =
    transitive-right-congruence-Semiring (semiring-Ring R) S

  concatenate-eq-sim-right-congruence-Ring :
    {x1 x2 y : type-Ring R} →
    x1 ＝ x2 → sim-right-congruence-Ring x2 y → sim-right-congruence-Ring x1 y
  concatenate-eq-sim-right-congruence-Ring =
    concatenate-eq-sim-right-congruence-Semiring (semiring-Ring R) S

  concatenate-sim-eq-right-congruence-Ring :
    {x y1 y2 : type-Ring R} →
    sim-right-congruence-Ring x y1 → y1 ＝ y2 → sim-right-congruence-Ring x y2
  concatenate-sim-eq-right-congruence-Ring =
    concatenate-sim-eq-right-congruence-Semiring (semiring-Ring R) S

  concatenate-eq-sim-eq-right-congruence-Ring :
    {x1 x2 y1 y2 : type-Ring R} →
    x1 ＝ x2 → sim-right-congruence-Ring x2 y1 →
    y1 ＝ y2 → sim-right-congruence-Ring x1 y2
  concatenate-eq-sim-eq-right-congruence-Ring =
    concatenate-eq-sim-eq-right-congruence-Semiring (semiring-Ring R) S

  is-additive-congruence-right-congruence-Ring :
    is-congruence-Monoid
      ( additive-monoid-Ring R)
      ( equivalence-relation-right-congruence-Ring)
  is-additive-congruence-right-congruence-Ring =
    is-additive-congruence-right-congruence-Semiring (semiring-Ring R) S

  congruence-ab-right-congruence-Ring : congruence-Ab l2 (ab-Ring R)
  pr1 congruence-ab-right-congruence-Ring =
    equivalence-relation-right-congruence-Ring
  pr2 congruence-ab-right-congruence-Ring =
    is-additive-congruence-right-congruence-Ring

  add-right-congruence-Ring :
    {x y u v : type-Ring R} →
    sim-right-congruence-Ring x y → sim-right-congruence-Ring u v →
    sim-right-congruence-Ring (add-Ring R x u) (add-Ring R y v)
  add-right-congruence-Ring =
    is-additive-congruence-right-congruence-Ring

  left-add-right-congruence-Ring :
    (x : type-Ring R) {y z : type-Ring R} →
    sim-right-congruence-Ring y z →
    sim-right-congruence-Ring (add-Ring R x y) (add-Ring R x z)
  left-add-right-congruence-Ring =
    left-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  right-add-right-congruence-Ring :
    {x y : type-Ring R} → sim-right-congruence-Ring x y →
    (z : type-Ring R) →
    sim-right-congruence-Ring (add-Ring R x z) (add-Ring R y z)
  right-add-right-congruence-Ring =
    right-add-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  sim-left-subtraction-zero-right-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-left-subtraction-zero-right-congruence-Ring =
    sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  map-sim-left-subtraction-zero-right-congruence-Ring :
    {x y : type-Ring R} → sim-right-congruence-Ring x y →
    sim-left-subtraction-zero-right-congruence-Ring x y
  map-sim-left-subtraction-zero-right-congruence-Ring =
    map-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  map-inv-sim-left-subtraction-zero-right-congruence-Ring :
    {x y : type-Ring R} →
    sim-left-subtraction-zero-right-congruence-Ring x y →
    sim-right-congruence-Ring x y
  map-inv-sim-left-subtraction-zero-right-congruence-Ring =
    map-inv-sim-left-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  sim-right-subtraction-zero-right-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-right-subtraction-zero-right-congruence-Ring =
    sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  map-sim-right-subtraction-zero-right-congruence-Ring :
    {x y : type-Ring R} → sim-right-congruence-Ring x y →
    sim-right-subtraction-zero-right-congruence-Ring x y
  map-sim-right-subtraction-zero-right-congruence-Ring =
    map-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  map-inv-sim-right-subtraction-zero-right-congruence-Ring :
    {x y : type-Ring R} → sim-right-subtraction-zero-right-congruence-Ring x y →
    sim-right-congruence-Ring x y
  map-inv-sim-right-subtraction-zero-right-congruence-Ring =
    map-inv-sim-right-subtraction-zero-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  neg-right-congruence-Ring :
    {x y : type-Ring R} → sim-right-congruence-Ring x y →
    sim-right-congruence-Ring (neg-Ring R x) (neg-Ring R y)
  neg-right-congruence-Ring =
    neg-congruence-Ab
      ( ab-Ring R)
      ( congruence-ab-right-congruence-Ring)

  right-mul-right-congruence-Ring :
    {x y : type-Ring R} (z : type-Ring R) →
    sim-right-congruence-Ring x y →
    sim-right-congruence-Ring (mul-Ring R x z) (mul-Ring R y z)
  right-mul-right-congruence-Ring z H =
    is-right-congruence-right-congruence-Ring H
```

## Properties

### Characterizing equality of right congruence relations of rings

```agda
relate-same-elements-right-congruence-Ring :
  {l1 l2 l3 : Level} (R : Ring l1) →
  right-congruence-Ring l2 R → right-congruence-Ring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-right-congruence-Ring R =
  relate-same-elements-right-congruence-Semiring (semiring-Ring R)

refl-relate-same-elements-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : right-congruence-Ring l2 R) →
  relate-same-elements-right-congruence-Ring R S S
refl-relate-same-elements-right-congruence-Ring R =
  refl-relate-same-elements-right-congruence-Semiring (semiring-Ring R)

is-torsorial-relate-same-elements-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S : right-congruence-Ring l2 R) →
  is-torsorial (relate-same-elements-right-congruence-Ring R S)
is-torsorial-relate-same-elements-right-congruence-Ring R =
  is-torsorial-relate-same-elements-right-congruence-Semiring
    ( semiring-Ring R)

relate-same-elements-eq-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : right-congruence-Ring l2 R) →
  S ＝ T → relate-same-elements-right-congruence-Ring R S T
relate-same-elements-eq-right-congruence-Ring R =
  relate-same-elements-eq-right-congruence-Semiring (semiring-Ring R)

is-equiv-relate-same-elements-eq-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : right-congruence-Ring l2 R) →
  is-equiv (relate-same-elements-eq-right-congruence-Ring R S T)
is-equiv-relate-same-elements-eq-right-congruence-Ring R =
  is-equiv-relate-same-elements-eq-right-congruence-Semiring
    ( semiring-Ring R)

extensionality-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : right-congruence-Ring l2 R) →
  (S ＝ T) ≃ relate-same-elements-right-congruence-Ring R S T
extensionality-right-congruence-Ring R =
  extensionality-right-congruence-Semiring (semiring-Ring R)

eq-relate-same-elements-right-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) (S T : right-congruence-Ring l2 R) →
  relate-same-elements-right-congruence-Ring R S T → S ＝ T
eq-relate-same-elements-right-congruence-Ring R =
  eq-relate-same-elements-right-congruence-Semiring (semiring-Ring R)
```
