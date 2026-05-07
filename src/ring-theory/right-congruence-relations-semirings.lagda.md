# Right congruence relations on semirings

```agda
module ring-theory.right-congruence-relations-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.telescopes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-monoids

open import ring-theory.semirings
```

</details>

## Idea

A
{{#concept "right congruence relation" Disambiguation="on a semiring" WD="congruence relation" WDID=Q8349849 Agda=right-congruence-Semiring}}
on a [semiring](ring-theory.semirings.md) `R` is a
[congruence relation](group-theory.congruence-relations-monoids.md) on the
underlying additive [monoid](group-theory.monoids.md) of `R` which is also a
congruence relation on the multiplicative monoid of `R`.

## Definition

### The type of congruence relations on the underlying additive monoid of a semiring

```agda
module _
  {l1 : Level} (l2 : Level) (R : Semiring l1)
  where

  congruence-additive-monoid-Semiring :
    UU (l1 ⊔ lsuc l2)
  congruence-additive-monoid-Semiring =
    congruence-Monoid l2 (additive-monoid-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1)
  (S : congruence-additive-monoid-Semiring l2 R)
  where

  sim-congruence-additive-monoid-Semiring :
    (x y : type-Semiring R) → UU l2
  sim-congruence-additive-monoid-Semiring =
    sim-congruence-Monoid (additive-monoid-Semiring R) S

  is-prop-sim-congruence-additive-monoid-Semiring :
    (x y : type-Semiring R) →
    is-prop (sim-congruence-additive-monoid-Semiring x y)
  is-prop-sim-congruence-additive-monoid-Semiring =
    is-prop-sim-congruence-Monoid (additive-monoid-Semiring R) S

  sim-prop-congruence-additive-monoid-Semiring :
    (x y : type-Semiring R) → Prop l2
  sim-prop-congruence-additive-monoid-Semiring =
    sim-prop-congruence-Monoid (additive-monoid-Semiring R) S
```

### The predicate of being a right congruence relation

```agda
module _
  {l1 l2 : Level} (R : Semiring l1)
  (S : congruence-Monoid l2 (additive-monoid-Semiring R))
  where

  is-right-congruence-congruence-additive-monoid-Semiring :
    UU (l1 ⊔ l2)
  is-right-congruence-congruence-additive-monoid-Semiring =
    {x y r : type-Semiring R}
    (H : sim-congruence-additive-monoid-Semiring R S x y) →
    sim-congruence-additive-monoid-Semiring R S
      ( mul-Semiring R x r)
      ( mul-Semiring R y r)

  is-prop-is-right-congruence-congruence-additive-monoid-Semiring :
    is-prop is-right-congruence-congruence-additive-monoid-Semiring
  is-prop-is-right-congruence-congruence-additive-monoid-Semiring =
    is-prop-iterated-implicit-Π 3
      ( λ _ _ _ →
        is-prop-function-type
          ( is-prop-sim-congruence-additive-monoid-Semiring R S _ _))

  is-right-congruence-prop-congruence-additive-monoid-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-right-congruence-prop-congruence-additive-monoid-Semiring =
    is-right-congruence-congruence-additive-monoid-Semiring
  pr2 is-right-congruence-prop-congruence-additive-monoid-Semiring =
    is-prop-is-right-congruence-congruence-additive-monoid-Semiring

module _
  {l1 l2 : Level} (R : Semiring l1)
  (S : equivalence-relation l2 (type-Semiring R))
  where

  is-right-congruence-equivalence-relation-Semiring :
    UU (l1 ⊔ l2)
  is-right-congruence-equivalence-relation-Semiring =
    Σ ( is-congruence-Monoid (additive-monoid-Semiring R) S)
      ( λ H → is-right-congruence-congruence-additive-monoid-Semiring R (S , H))

  is-prop-is-right-congruence-equivalence-relation-Semiring :
    is-prop is-right-congruence-equivalence-relation-Semiring
  is-prop-is-right-congruence-equivalence-relation-Semiring =
    is-prop-Σ
      ( is-prop-is-congruence-Monoid (additive-monoid-Semiring R) S)
      ( λ H →
        is-prop-is-right-congruence-congruence-additive-monoid-Semiring R
          ( S , H))

  is-right-congruence-prop-equivalence-relation-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-right-congruence-prop-equivalence-relation-Semiring =
    is-right-congruence-equivalence-relation-Semiring
  pr2 is-right-congruence-prop-equivalence-relation-Semiring =
    is-prop-is-right-congruence-equivalence-relation-Semiring

right-congruence-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
right-congruence-Semiring l2 R =
  Σ ( congruence-additive-monoid-Semiring l2 R)
    ( is-right-congruence-congruence-additive-monoid-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (S : right-congruence-Semiring l2 R)
  where

  congruence-additive-monoid-right-congruence-Semiring :
    congruence-additive-monoid-Semiring l2 R
  congruence-additive-monoid-right-congruence-Semiring =
    pr1 S

  is-right-congruence-right-congruence-Semiring :
    is-right-congruence-congruence-additive-monoid-Semiring R
      congruence-additive-monoid-right-congruence-Semiring
  is-right-congruence-right-congruence-Semiring =
    pr2 S

  equivalence-relation-right-congruence-Semiring :
    equivalence-relation l2 (type-Semiring R)
  equivalence-relation-right-congruence-Semiring =
    equivalence-relation-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  sim-right-congruence-Semiring :
    (x y : type-Semiring R) → UU l2
  sim-right-congruence-Semiring =
    sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  is-prop-sim-right-congruence-Semiring :
    (x y : type-Semiring R) → is-prop (sim-right-congruence-Semiring x y)
  is-prop-sim-right-congruence-Semiring =
    is-prop-sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  sim-prop-right-congruence-Semiring :
    (x y : type-Semiring R) → Prop l2
  sim-prop-right-congruence-Semiring =
    sim-prop-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  refl-right-congruence-Semiring :
    is-reflexive sim-right-congruence-Semiring
  refl-right-congruence-Semiring =
    refl-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  symmetric-right-congruence-Semiring :
    is-symmetric sim-right-congruence-Semiring
  symmetric-right-congruence-Semiring =
    symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  equiv-symmetric-right-congruence-Semiring :
    (x y : type-Semiring R) →
    sim-right-congruence-Semiring x y ≃ sim-right-congruence-Semiring y x
  equiv-symmetric-right-congruence-Semiring =
    equiv-symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  transitive-right-congruence-Semiring :
    is-transitive sim-right-congruence-Semiring
  transitive-right-congruence-Semiring =
    transitive-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)

  is-additive-congruence-right-congruence-Semiring :
    is-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( equivalence-relation-right-congruence-Semiring)
  is-additive-congruence-right-congruence-Semiring =
    mul-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring)
```

## Properties

### Characterizing equality of right congruence relations of semirings

```agda
relate-same-elements-right-congruence-Semiring :
  {l1 l2 l3 : Level} (R : Semiring l1) →
  right-congruence-Semiring l2 R → right-congruence-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-right-congruence-Semiring R S T =
  relate-same-elements-equivalence-relation
    ( equivalence-relation-right-congruence-Semiring R S)
    ( equivalence-relation-right-congruence-Semiring R T)

refl-relate-same-elements-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : right-congruence-Semiring l2 R) →
  relate-same-elements-right-congruence-Semiring R S S
refl-relate-same-elements-right-congruence-Semiring R S =
  refl-relate-same-elements-equivalence-relation
    ( equivalence-relation-right-congruence-Semiring R S)

is-torsorial-relate-same-elements-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : right-congruence-Semiring l2 R) →
  is-torsorial (relate-same-elements-right-congruence-Semiring R S)
is-torsorial-relate-same-elements-right-congruence-Semiring R S =
  is-torsorial-Eq-subtype
    ( is-torsorial-relate-same-elements-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-right-congruence-Semiring R S))
    ( is-prop-is-right-congruence-congruence-additive-monoid-Semiring R)
    ( congruence-additive-monoid-right-congruence-Semiring R S)
    ( refl-relate-same-elements-right-congruence-Semiring R S)
    ( is-right-congruence-right-congruence-Semiring R S)

relate-same-elements-eq-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : right-congruence-Semiring l2 R) →
  S ＝ T → relate-same-elements-right-congruence-Semiring R S T
relate-same-elements-eq-right-congruence-Semiring R S .S refl =
  refl-relate-same-elements-right-congruence-Semiring R S

is-equiv-relate-same-elements-eq-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : right-congruence-Semiring l2 R) →
  is-equiv (relate-same-elements-eq-right-congruence-Semiring R S T)
is-equiv-relate-same-elements-eq-right-congruence-Semiring R S =
    fundamental-theorem-id
      ( is-torsorial-relate-same-elements-right-congruence-Semiring R S)
      ( relate-same-elements-eq-right-congruence-Semiring R S)

extensionality-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : right-congruence-Semiring l2 R) →
  (S ＝ T) ≃ relate-same-elements-right-congruence-Semiring R S T
pr1 (extensionality-right-congruence-Semiring R S T) =
  relate-same-elements-eq-right-congruence-Semiring R S T
pr2 (extensionality-right-congruence-Semiring R S T) =
  is-equiv-relate-same-elements-eq-right-congruence-Semiring R S T

eq-relate-same-elements-right-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : right-congruence-Semiring l2 R) →
  relate-same-elements-right-congruence-Semiring R S T → S ＝ T
eq-relate-same-elements-right-congruence-Semiring R S T =
  map-inv-equiv (extensionality-right-congruence-Semiring R S T)
```
