# Congruence relations on monoids

```agda
module group-theory.congruence-relations-monoids where
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

open import group-theory.congruence-relations-semigroups
open import group-theory.monoids
```

</details>

## Idea

A congruence relation on a monoid `M` is a congruence relation on the underlying
semigroup of `M`.

## Definition

```agda
is-congruence-prop-Monoid :
  {l1 l2 : Level} (M : Monoid l1) →
  equivalence-relation l2 (type-Monoid M) → Prop (l1 ⊔ l2)
is-congruence-prop-Monoid M = is-congruence-prop-Semigroup (semigroup-Monoid M)

is-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) →
  equivalence-relation l2 (type-Monoid M) → UU (l1 ⊔ l2)
is-congruence-Monoid M R =
  is-congruence-Semigroup (semigroup-Monoid M) R

is-prop-is-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1)
  (R : equivalence-relation l2 (type-Monoid M)) →
  is-prop (is-congruence-Monoid M R)
is-prop-is-congruence-Monoid M =
  is-prop-is-congruence-Semigroup (semigroup-Monoid M)

congruence-Monoid : {l : Level} (l2 : Level) (M : Monoid l) → UU (l ⊔ lsuc l2)
congruence-Monoid l2 M =
  Σ (equivalence-relation l2 (type-Monoid M)) (is-congruence-Monoid M)

module _
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  where

  equivalence-relation-congruence-Monoid :
    equivalence-relation l2 (type-Monoid M)
  equivalence-relation-congruence-Monoid = pr1 R

  prop-congruence-Monoid : Relation-Prop l2 (type-Monoid M)
  prop-congruence-Monoid =
    prop-equivalence-relation equivalence-relation-congruence-Monoid

  sim-congruence-Monoid : (x y : type-Monoid M) → UU l2
  sim-congruence-Monoid =
    sim-equivalence-relation equivalence-relation-congruence-Monoid

  is-prop-sim-congruence-Monoid :
    (x y : type-Monoid M) → is-prop (sim-congruence-Monoid x y)
  is-prop-sim-congruence-Monoid =
    is-prop-sim-equivalence-relation equivalence-relation-congruence-Monoid

  concatenate-sim-eq-congruence-Monoid :
    {x y z : type-Monoid M} → sim-congruence-Monoid x y → y ＝ z →
    sim-congruence-Monoid x z
  concatenate-sim-eq-congruence-Monoid H refl = H

  concatenate-eq-sim-congruence-Monoid :
    {x y z : type-Monoid M} → x ＝ y → sim-congruence-Monoid y z →
    sim-congruence-Monoid x z
  concatenate-eq-sim-congruence-Monoid refl H = H

  concatenate-eq-sim-eq-congruence-Monoid :
    {x y z w : type-Monoid M} → x ＝ y → sim-congruence-Monoid y z →
    z ＝ w → sim-congruence-Monoid x w
  concatenate-eq-sim-eq-congruence-Monoid refl H refl = H

  refl-congruence-Monoid : is-reflexive sim-congruence-Monoid
  refl-congruence-Monoid =
    refl-equivalence-relation equivalence-relation-congruence-Monoid

  symmetric-congruence-Monoid : is-symmetric sim-congruence-Monoid
  symmetric-congruence-Monoid =
    symmetric-equivalence-relation equivalence-relation-congruence-Monoid

  equiv-symmetric-congruence-Monoid :
    (x y : type-Monoid M) →
    sim-congruence-Monoid x y ≃ sim-congruence-Monoid y x
  equiv-symmetric-congruence-Monoid x y =
    equiv-symmetric-equivalence-relation equivalence-relation-congruence-Monoid

  transitive-congruence-Monoid : is-transitive sim-congruence-Monoid
  transitive-congruence-Monoid =
    transitive-equivalence-relation equivalence-relation-congruence-Monoid

  mul-congruence-Monoid :
    is-congruence-Monoid M equivalence-relation-congruence-Monoid
  mul-congruence-Monoid = pr2 R
```

## Properties

### Extensionality of the type of congruence relations on a monoid

```agda
relate-same-elements-congruence-Monoid :
  {l1 l2 l3 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  (S : congruence-Monoid l3 M) → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Monoid M =
  relate-same-elements-congruence-Semigroup
    ( semigroup-Monoid M)

refl-relate-same-elements-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M) →
  relate-same-elements-congruence-Monoid M R R
refl-relate-same-elements-congruence-Monoid M =
  refl-relate-same-elements-congruence-Semigroup (semigroup-Monoid M)

is-torsorial-relate-same-elements-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M) →
  is-torsorial (relate-same-elements-congruence-Monoid M R)
is-torsorial-relate-same-elements-congruence-Monoid M =
  is-torsorial-relate-same-elements-congruence-Semigroup (semigroup-Monoid M)

relate-same-elements-eq-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : congruence-Monoid l2 M) →
  R ＝ S → relate-same-elements-congruence-Monoid M R S
relate-same-elements-eq-congruence-Monoid M =
  relate-same-elements-eq-congruence-Semigroup (semigroup-Monoid M)

is-equiv-relate-same-elements-eq-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : congruence-Monoid l2 M) →
  is-equiv (relate-same-elements-eq-congruence-Monoid M R S)
is-equiv-relate-same-elements-eq-congruence-Monoid M =
  is-equiv-relate-same-elements-eq-congruence-Semigroup (semigroup-Monoid M)

extensionality-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : congruence-Monoid l2 M) →
  (R ＝ S) ≃ relate-same-elements-congruence-Monoid M R S
extensionality-congruence-Monoid M =
  extensionality-congruence-Semigroup (semigroup-Monoid M)

eq-relate-same-elements-congruence-Monoid :
  {l1 l2 : Level} (M : Monoid l1) (R S : congruence-Monoid l2 M) →
  relate-same-elements-congruence-Monoid M R S → R ＝ S
eq-relate-same-elements-congruence-Monoid M =
  eq-relate-same-elements-congruence-Semigroup
    ( semigroup-Monoid M)
```
