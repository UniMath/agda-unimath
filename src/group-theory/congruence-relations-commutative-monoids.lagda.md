# Congruence relations on commutative monoids

```agda
module group-theory.congruence-relations-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-products-propositions
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.congruence-relations-monoids
```

</details>

## Idea

A congruence relation on a commutative monoid `M` is a congruence relation on
the underlying monoid of `M`.

## Definition

```agda
is-congruence-prop-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) →
  equivalence-relation l2 (type-Commutative-Monoid M) → Prop (l1 ⊔ l2)
is-congruence-prop-Commutative-Monoid M =
  is-congruence-prop-Monoid (monoid-Commutative-Monoid M)

is-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) →
  equivalence-relation l2 (type-Commutative-Monoid M) → UU (l1 ⊔ l2)
is-congruence-Commutative-Monoid M =
  is-congruence-Monoid (monoid-Commutative-Monoid M)

is-prop-is-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : equivalence-relation l2 (type-Commutative-Monoid M)) →
  is-prop (is-congruence-Commutative-Monoid M R)
is-prop-is-congruence-Commutative-Monoid M =
  is-prop-is-congruence-Monoid (monoid-Commutative-Monoid M)

congruence-Commutative-Monoid :
  {l : Level} (l2 : Level) (M : Commutative-Monoid l) → UU (l ⊔ lsuc l2)
congruence-Commutative-Monoid l2 M =
  congruence-Monoid l2 (monoid-Commutative-Monoid M)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M)
  where

  equivalence-relation-congruence-Commutative-Monoid :
    equivalence-relation l2 (type-Commutative-Monoid M)
  equivalence-relation-congruence-Commutative-Monoid =
    equivalence-relation-congruence-Monoid (monoid-Commutative-Monoid M) R

  prop-congruence-Commutative-Monoid :
    Relation-Prop l2 (type-Commutative-Monoid M)
  prop-congruence-Commutative-Monoid =
    prop-congruence-Monoid (monoid-Commutative-Monoid M) R

  sim-congruence-Commutative-Monoid : (x y : type-Commutative-Monoid M) → UU l2
  sim-congruence-Commutative-Monoid =
    sim-congruence-Monoid (monoid-Commutative-Monoid M) R

  is-prop-sim-congruence-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    is-prop (sim-congruence-Commutative-Monoid x y)
  is-prop-sim-congruence-Commutative-Monoid =
    is-prop-sim-congruence-Monoid (monoid-Commutative-Monoid M) R

  concatenate-sim-eq-congruence-Commutative-Monoid :
    {x y z : type-Commutative-Monoid M} →
    sim-congruence-Commutative-Monoid x y → y ＝ z →
    sim-congruence-Commutative-Monoid x z
  concatenate-sim-eq-congruence-Commutative-Monoid =
    concatenate-sim-eq-congruence-Monoid (monoid-Commutative-Monoid M) R

  concatenate-eq-sim-congruence-Commutative-Monoid :
    {x y z : type-Commutative-Monoid M} → x ＝ y →
    sim-congruence-Commutative-Monoid y z →
    sim-congruence-Commutative-Monoid x z
  concatenate-eq-sim-congruence-Commutative-Monoid =
    concatenate-eq-sim-congruence-Monoid (monoid-Commutative-Monoid M) R

  concatenate-eq-sim-eq-congruence-Commutative-Monoid :
    {x y z w : type-Commutative-Monoid M} → x ＝ y →
    sim-congruence-Commutative-Monoid y z →
    z ＝ w → sim-congruence-Commutative-Monoid x w
  concatenate-eq-sim-eq-congruence-Commutative-Monoid =
    concatenate-eq-sim-eq-congruence-Monoid (monoid-Commutative-Monoid M) R

  refl-congruence-Commutative-Monoid :
    is-reflexive sim-congruence-Commutative-Monoid
  refl-congruence-Commutative-Monoid =
    refl-congruence-Monoid (monoid-Commutative-Monoid M) R

  symmetric-congruence-Commutative-Monoid :
    is-symmetric sim-congruence-Commutative-Monoid
  symmetric-congruence-Commutative-Monoid =
    symmetric-congruence-Monoid (monoid-Commutative-Monoid M) R

  equiv-symmetric-congruence-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    sim-congruence-Commutative-Monoid x y ≃
    sim-congruence-Commutative-Monoid y x
  equiv-symmetric-congruence-Commutative-Monoid =
    equiv-symmetric-congruence-Monoid (monoid-Commutative-Monoid M) R

  transitive-congruence-Commutative-Monoid :
    is-transitive sim-congruence-Commutative-Monoid
  transitive-congruence-Commutative-Monoid =
    transitive-congruence-Monoid (monoid-Commutative-Monoid M) R

  mul-congruence-Commutative-Monoid :
    is-congruence-Commutative-Monoid M
      equivalence-relation-congruence-Commutative-Monoid
  mul-congruence-Commutative-Monoid =
    mul-congruence-Monoid (monoid-Commutative-Monoid M) R
```

## Properties

### Extensionality of the type of congruence relations on a monoid

```agda
relate-same-elements-congruence-Commutative-Monoid :
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M)
  (S : congruence-Commutative-Monoid l3 M) → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Commutative-Monoid M =
  relate-same-elements-congruence-Monoid (monoid-Commutative-Monoid M)

refl-relate-same-elements-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M) →
  relate-same-elements-congruence-Commutative-Monoid M R R
refl-relate-same-elements-congruence-Commutative-Monoid M =
  refl-relate-same-elements-congruence-Monoid (monoid-Commutative-Monoid M)

is-torsorial-relate-same-elements-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M) →
  is-torsorial (relate-same-elements-congruence-Commutative-Monoid M R)
is-torsorial-relate-same-elements-congruence-Commutative-Monoid M =
  is-torsorial-relate-same-elements-congruence-Monoid
    ( monoid-Commutative-Monoid M)

relate-same-elements-eq-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : congruence-Commutative-Monoid l2 M) →
  R ＝ S → relate-same-elements-congruence-Commutative-Monoid M R S
relate-same-elements-eq-congruence-Commutative-Monoid M =
  relate-same-elements-eq-congruence-Monoid (monoid-Commutative-Monoid M)

is-equiv-relate-same-elements-eq-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : congruence-Commutative-Monoid l2 M) →
  is-equiv (relate-same-elements-eq-congruence-Commutative-Monoid M R S)
is-equiv-relate-same-elements-eq-congruence-Commutative-Monoid M =
  is-equiv-relate-same-elements-eq-congruence-Monoid
    ( monoid-Commutative-Monoid M)

extensionality-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : congruence-Commutative-Monoid l2 M) →
  (R ＝ S) ≃ relate-same-elements-congruence-Commutative-Monoid M R S
extensionality-congruence-Commutative-Monoid M =
  extensionality-congruence-Monoid (monoid-Commutative-Monoid M)

eq-relate-same-elements-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : congruence-Commutative-Monoid l2 M) →
  relate-same-elements-congruence-Commutative-Monoid M R S → R ＝ S
eq-relate-same-elements-congruence-Commutative-Monoid M =
  eq-relate-same-elements-congruence-Monoid
    ( monoid-Commutative-Monoid M)
```
