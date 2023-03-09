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
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids

open import ring-theory.congruence-relations-semirings
open import ring-theory.rings
```

</details>

## Idea

A congruence relation on a ring `R` is a congruence relation on the
underlying semiring of `R`.

## Definition

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-congruence-Ring :
    {l2 : Level} → congruence-Ab l2 (ab-Ring R) → UU (l1 ⊔ l2)
  is-congruence-Ring = is-congruence-Semiring (semiring-Ring R)

  is-congruence-eq-rel-Ring :
    {l2 : Level} (S : Eq-Rel l2 (type-Ring R)) → UU (l1 ⊔ l2)
  is-congruence-eq-rel-Ring S =
    is-congruence-eq-rel-Semiring (semiring-Ring R) S

congruence-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
congruence-Ring l2 R = congruence-Semiring l2 (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  congruence-ab-congruence-Ring : congruence-Ab l2 (ab-Ring R)
  congruence-ab-congruence-Ring =
    congruence-additive-monoid-congruence-Semiring (semiring-Ring R) S

  eq-rel-congruence-Ring : Eq-Rel l2 (type-Ring R)
  eq-rel-congruence-Ring =
    eq-rel-congruence-Semiring (semiring-Ring R) S

  prop-congruence-Ring : Rel-Prop l2 (type-Ring R)
  prop-congruence-Ring = prop-congruence-Semiring (semiring-Ring R) S

  sim-congruence-Ring : (x y : type-Ring R) → UU l2
  sim-congruence-Ring = sim-congruence-Semiring (semiring-Ring R) S

  is-prop-sim-congruence-Ring :
    (x y : type-Ring R) → is-prop (sim-congruence-Ring x y)
  is-prop-sim-congruence-Ring =
    is-prop-sim-congruence-Semiring (semiring-Ring R) S

  refl-congruence-Ring :
    is-reflexive-Rel-Prop prop-congruence-Ring
  refl-congruence-Ring = refl-congruence-Semiring (semiring-Ring R) S

  symm-congruence-Ring :
    is-symmetric-Rel-Prop prop-congruence-Ring
  symm-congruence-Ring = symm-congruence-Semiring (semiring-Ring R) S

  equiv-symm-congruence-Ring :
    (x y : type-Ring R) →
    sim-congruence-Ring x y ≃ sim-congruence-Ring y x
  equiv-symm-congruence-Ring =
    equiv-symm-congruence-Semiring (semiring-Ring R) S

  trans-congruence-Ring :
    is-transitive-Rel-Prop prop-congruence-Ring
  trans-congruence-Ring =
    trans-congruence-Semiring (semiring-Ring R) S

  add-congruence-Ring :
    is-congruence-Ab (ab-Ring R) eq-rel-congruence-Ring
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
      ( eq-rel-congruence-Ring)
  mul-congruence-Ring = pr2 S

construct-congruence-Ring :
  {l1 l2 : Level} (R : Ring l1) →
  (S : Eq-Rel l2 (type-Ring R)) →
  is-congruence-Ab (ab-Ring R) S →
  is-congruence-Monoid (multiplicative-monoid-Ring R) S →
  congruence-Ring l2 R
pr1 (pr1 (construct-congruence-Ring R S H K)) = S
pr2 (pr1 (construct-congruence-Ring R S H K)) = H
pr2 (construct-congruence-Ring R S H K) = K
```
