# Saturated congruence relations on commutative monoids

```agda
module group-theory.saturated-congruence-relations-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.congruence-relations-commutative-monoids
```

</details>

## Idea

For any commutative monoid `M`, the type of normal submonoids is a retract of
the type of congruence relations on `M`. A congruence relation on `M` is said to
be **saturated** if it is in the image of the inclusion of the normal submonoids
of `M` into the congruence relations on `M`.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : congruence-Commutative-Monoid l2 M)
  where

  is-saturated-prop-congruence-Commutative-Monoid : Prop (l1 ⊔ l2)
  is-saturated-prop-congruence-Commutative-Monoid =
    Π-Prop
      ( type-Commutative-Monoid M)
      ( λ x →
        Π-Prop
          ( type-Commutative-Monoid M)
          ( λ y →
            function-Prop
              ( (u : type-Commutative-Monoid M) →
                ( sim-congruence-Commutative-Monoid M R
                  ( mul-Commutative-Monoid M u x)
                  ( unit-Commutative-Monoid M)) ↔
                ( sim-congruence-Commutative-Monoid M R
                  ( mul-Commutative-Monoid M u y)
                  ( unit-Commutative-Monoid M)))
              ( prop-congruence-Commutative-Monoid M R x y)))

  is-saturated-congruence-Commutative-Monoid : UU (l1 ⊔ l2)
  is-saturated-congruence-Commutative-Monoid =
    type-Prop is-saturated-prop-congruence-Commutative-Monoid

  is-prop-is-saturated-congruence-Commutative-Monoid :
    is-prop is-saturated-congruence-Commutative-Monoid
  is-prop-is-saturated-congruence-Commutative-Monoid =
    is-prop-type-Prop is-saturated-prop-congruence-Commutative-Monoid

saturated-congruence-Commutative-Monoid :
  {l1 : Level} (l2 : Level) (M : Commutative-Monoid l1) → UU (l1 ⊔ lsuc l2)
saturated-congruence-Commutative-Monoid l2 M =
  Σ ( congruence-Commutative-Monoid l2 M)
    ( is-saturated-congruence-Commutative-Monoid M)

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid l2 M)
  where

  congruence-saturated-congruence-Commutative-Monoid :
    congruence-Commutative-Monoid l2 M
  congruence-saturated-congruence-Commutative-Monoid = pr1 R

  is-saturated-saturated-congruence-Commutative-Monoid :
    is-saturated-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid
  is-saturated-saturated-congruence-Commutative-Monoid = pr2 R

  equivalence-relation-saturated-congruence-Commutative-Monoid :
    equivalence-relation l2 (type-Commutative-Monoid M)
  equivalence-relation-saturated-congruence-Commutative-Monoid =
    equivalence-relation-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  prop-saturated-congruence-Commutative-Monoid :
    Relation-Prop l2 (type-Commutative-Monoid M)
  prop-saturated-congruence-Commutative-Monoid =
    prop-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  sim-saturated-congruence-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) → UU l2
  sim-saturated-congruence-Commutative-Monoid =
    sim-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  is-prop-sim-saturated-congruence-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
      is-prop (sim-saturated-congruence-Commutative-Monoid x y)
  is-prop-sim-saturated-congruence-Commutative-Monoid =
    is-prop-sim-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  concatenate-sim-eq-saturated-congruence-Commutative-Monoid :
    {x y z : type-Commutative-Monoid M} →
    sim-saturated-congruence-Commutative-Monoid x y → y ＝ z →
    sim-saturated-congruence-Commutative-Monoid x z
  concatenate-sim-eq-saturated-congruence-Commutative-Monoid =
    concatenate-sim-eq-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  concatenate-eq-sim-saturated-congruence-Commutative-Monoid :
    {x y z : type-Commutative-Monoid M} → x ＝ y →
    sim-saturated-congruence-Commutative-Monoid y z →
    sim-saturated-congruence-Commutative-Monoid x z
  concatenate-eq-sim-saturated-congruence-Commutative-Monoid =
    concatenate-eq-sim-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  concatenate-eq-sim-eq-saturated-congruence-Commutative-Monoid :
    {x y z w : type-Commutative-Monoid M} → x ＝ y →
    sim-saturated-congruence-Commutative-Monoid y z →
    z ＝ w → sim-saturated-congruence-Commutative-Monoid x w
  concatenate-eq-sim-eq-saturated-congruence-Commutative-Monoid =
    concatenate-eq-sim-eq-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  refl-saturated-congruence-Commutative-Monoid :
    is-reflexive sim-saturated-congruence-Commutative-Monoid
  refl-saturated-congruence-Commutative-Monoid =
    refl-congruence-Commutative-Monoid M
    congruence-saturated-congruence-Commutative-Monoid

  symmetric-saturated-congruence-Commutative-Monoid :
    is-symmetric sim-saturated-congruence-Commutative-Monoid
  symmetric-saturated-congruence-Commutative-Monoid =
    symmetric-congruence-Commutative-Monoid M
    congruence-saturated-congruence-Commutative-Monoid

  equiv-symmetric-saturated-congruence-Commutative-Monoid :
    (x y : type-Commutative-Monoid M) →
    sim-saturated-congruence-Commutative-Monoid x y ≃
    sim-saturated-congruence-Commutative-Monoid y x
  equiv-symmetric-saturated-congruence-Commutative-Monoid =
    equiv-symmetric-congruence-Commutative-Monoid M
    congruence-saturated-congruence-Commutative-Monoid

  transitive-saturated-congruence-Commutative-Monoid :
    is-transitive sim-saturated-congruence-Commutative-Monoid
  transitive-saturated-congruence-Commutative-Monoid =
    transitive-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid

  mul-saturated-congruence-Commutative-Monoid :
    is-congruence-Commutative-Monoid M
      equivalence-relation-saturated-congruence-Commutative-Monoid
  mul-saturated-congruence-Commutative-Monoid =
    mul-congruence-Commutative-Monoid M
      congruence-saturated-congruence-Commutative-Monoid
```

## Properties

### Extensionality of the type of saturated congruence relations on a commutative monoid

```agda
relate-same-elements-saturated-congruence-Commutative-Monoid :
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid l2 M)
  (S : saturated-congruence-Commutative-Monoid l3 M) → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-saturated-congruence-Commutative-Monoid M R S =
  relate-same-elements-congruence-Commutative-Monoid M
    ( congruence-saturated-congruence-Commutative-Monoid M R)
    ( congruence-saturated-congruence-Commutative-Monoid M S)

refl-relate-same-elements-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid l2 M) →
  relate-same-elements-saturated-congruence-Commutative-Monoid M R R
refl-relate-same-elements-saturated-congruence-Commutative-Monoid M R =
  refl-relate-same-elements-congruence-Commutative-Monoid M
    ( congruence-saturated-congruence-Commutative-Monoid M R)

is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R : saturated-congruence-Commutative-Monoid l2 M) →
  is-torsorial
    ( relate-same-elements-saturated-congruence-Commutative-Monoid M R)
is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoid
  M R =
  is-torsorial-Eq-subtype
    ( is-torsorial-relate-same-elements-congruence-Commutative-Monoid M
      ( congruence-saturated-congruence-Commutative-Monoid M R))
    ( is-prop-is-saturated-congruence-Commutative-Monoid M)
    ( congruence-saturated-congruence-Commutative-Monoid M R)
    ( refl-relate-same-elements-congruence-Commutative-Monoid M
      ( congruence-saturated-congruence-Commutative-Monoid M R))
    ( is-saturated-saturated-congruence-Commutative-Monoid M R)

relate-same-elements-eq-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : saturated-congruence-Commutative-Monoid l2 M) →
  R ＝ S → relate-same-elements-saturated-congruence-Commutative-Monoid M R S
relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R .R refl =
  refl-relate-same-elements-saturated-congruence-Commutative-Monoid M R

is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : saturated-congruence-Commutative-Monoid l2 M) →
  is-equiv
    ( relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R S)
is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R =
  fundamental-theorem-id
    ( is-torsorial-relate-same-elements-saturated-congruence-Commutative-Monoid
      ( M)
      ( R))
    ( relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R)

extensionality-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : saturated-congruence-Commutative-Monoid l2 M) →
  (R ＝ S) ≃ relate-same-elements-saturated-congruence-Commutative-Monoid M R S
pr1 (extensionality-saturated-congruence-Commutative-Monoid M R S) =
  relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R S
pr2 (extensionality-saturated-congruence-Commutative-Monoid M R S) =
  is-equiv-relate-same-elements-eq-saturated-congruence-Commutative-Monoid M R S

eq-relate-same-elements-saturated-congruence-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (R S : saturated-congruence-Commutative-Monoid l2 M) →
  relate-same-elements-saturated-congruence-Commutative-Monoid M R S → R ＝ S
eq-relate-same-elements-saturated-congruence-Commutative-Monoid
  M R S =
  map-inv-equiv (extensionality-saturated-congruence-Commutative-Monoid M R S)
```

## See also

- Not every congruence relation on a commutative monoid is saturated. For an
  example, see the commutative monoid
  [`ℕ-Max`](elementary-number-theory.monoid-of-natural-numbers-with-maximum.md).
