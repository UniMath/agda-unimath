# Left congruence relations on semirings

```agda
module ring-theory.left-congruence-relations-semirings where
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
{{#concept "left congruence relation" Disambiguation="on a semiring" WD="congruence relation" WDID=Q8349849 Agda=left-congruence-Semiring}}
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

### The predicate of being a left congruence relation

```agda
module _
  {l1 l2 : Level} (R : Semiring l1)
  (S : congruence-Monoid l2 (additive-monoid-Semiring R))
  where

  is-left-congruence-congruence-additive-monoid-Semiring :
    UU (l1 ⊔ l2)
  is-left-congruence-congruence-additive-monoid-Semiring =
    {r x y : type-Semiring R}
    (H : sim-congruence-additive-monoid-Semiring R S x y) →
    sim-congruence-additive-monoid-Semiring R S
      ( mul-Semiring R r x)
      ( mul-Semiring R r y)

  is-prop-is-left-congruence-congruence-additive-monoid-Semiring :
    is-prop is-left-congruence-congruence-additive-monoid-Semiring
  is-prop-is-left-congruence-congruence-additive-monoid-Semiring =
    is-prop-iterated-implicit-Π 3
      ( λ _ _ _ →
        is-prop-function-type
          ( is-prop-sim-congruence-additive-monoid-Semiring R S _ _))

  is-left-congruence-prop-congruence-additive-monoid-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-left-congruence-prop-congruence-additive-monoid-Semiring =
    is-left-congruence-congruence-additive-monoid-Semiring
  pr2 is-left-congruence-prop-congruence-additive-monoid-Semiring =
    is-prop-is-left-congruence-congruence-additive-monoid-Semiring

module _
  {l1 l2 : Level} (R : Semiring l1)
  (S : equivalence-relation l2 (type-Semiring R))
  where

  is-left-congruence-equivalence-relation-Semiring :
    UU (l1 ⊔ l2)
  is-left-congruence-equivalence-relation-Semiring =
    Σ ( is-congruence-Monoid (additive-monoid-Semiring R) S)
      ( λ H → is-left-congruence-congruence-additive-monoid-Semiring R (S , H))

  is-prop-is-left-congruence-equivalence-relation-Semiring :
    is-prop is-left-congruence-equivalence-relation-Semiring
  is-prop-is-left-congruence-equivalence-relation-Semiring =
    is-prop-Σ
      ( is-prop-is-congruence-Monoid (additive-monoid-Semiring R) S)
      ( λ H →
        is-prop-is-left-congruence-congruence-additive-monoid-Semiring R
          ( S , H))

  is-left-congruence-prop-equivalence-relation-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-left-congruence-prop-equivalence-relation-Semiring =
    is-left-congruence-equivalence-relation-Semiring
  pr2 is-left-congruence-prop-equivalence-relation-Semiring =
    is-prop-is-left-congruence-equivalence-relation-Semiring

left-congruence-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
left-congruence-Semiring l2 R =
  Σ ( congruence-additive-monoid-Semiring l2 R)
    ( is-left-congruence-congruence-additive-monoid-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (S : left-congruence-Semiring l2 R)
  where

  congruence-additive-monoid-left-congruence-Semiring :
    congruence-additive-monoid-Semiring l2 R
  congruence-additive-monoid-left-congruence-Semiring =
    pr1 S

  is-left-congruence-left-congruence-Semiring :
    is-left-congruence-congruence-additive-monoid-Semiring R
      congruence-additive-monoid-left-congruence-Semiring
  is-left-congruence-left-congruence-Semiring =
    pr2 S

  equivalence-relation-left-congruence-Semiring :
    equivalence-relation l2 (type-Semiring R)
  equivalence-relation-left-congruence-Semiring =
    equivalence-relation-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  sim-left-congruence-Semiring :
    (x y : type-Semiring R) → UU l2
  sim-left-congruence-Semiring =
    sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  is-prop-sim-left-congruence-Semiring :
    (x y : type-Semiring R) → is-prop (sim-left-congruence-Semiring x y)
  is-prop-sim-left-congruence-Semiring =
    is-prop-sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  sim-prop-left-congruence-Semiring :
    (x y : type-Semiring R) → Prop l2
  sim-prop-left-congruence-Semiring =
    sim-prop-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  refl-left-congruence-Semiring :
    is-reflexive sim-left-congruence-Semiring
  refl-left-congruence-Semiring =
    refl-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  symmetric-left-congruence-Semiring :
    is-symmetric sim-left-congruence-Semiring
  symmetric-left-congruence-Semiring =
    symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  equiv-symmetric-left-congruence-Semiring :
    (x y : type-Semiring R) →
    sim-left-congruence-Semiring x y ≃ sim-left-congruence-Semiring y x
  equiv-symmetric-left-congruence-Semiring =
    equiv-symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  transitive-left-congruence-Semiring :
    is-transitive sim-left-congruence-Semiring
  transitive-left-congruence-Semiring =
    transitive-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  concatenate-eq-sim-left-congruence-Semiring :
    {x1 x2 y : type-Semiring R} →
    x1 ＝ x2 → sim-left-congruence-Semiring x2 y →
    sim-left-congruence-Semiring x1 y
  concatenate-eq-sim-left-congruence-Semiring =
    concatenate-eq-sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  concatenate-sim-eq-left-congruence-Semiring :
    {x y1 y2 : type-Semiring R} →
    sim-left-congruence-Semiring x y1 → y1 ＝ y2 →
    sim-left-congruence-Semiring x y2
  concatenate-sim-eq-left-congruence-Semiring =
    concatenate-sim-eq-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  concatenate-eq-sim-eq-left-congruence-Semiring :
    {x1 x2 y1 y2 : type-Semiring R} →
    x1 ＝ x2 → sim-left-congruence-Semiring x2 y1 →
    y1 ＝ y2 → sim-left-congruence-Semiring x1 y2
  concatenate-eq-sim-eq-left-congruence-Semiring =
    concatenate-eq-sim-eq-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)

  is-additive-congruence-left-congruence-Semiring :
    is-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( equivalence-relation-left-congruence-Semiring)
  is-additive-congruence-left-congruence-Semiring =
    mul-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring)
```

## Properties

### Characterizing equality of left congruence relations of semirings

```agda
relate-same-elements-left-congruence-Semiring :
  {l1 l2 l3 : Level} (R : Semiring l1) →
  left-congruence-Semiring l2 R → left-congruence-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-left-congruence-Semiring R S T =
  relate-same-elements-equivalence-relation
    ( equivalence-relation-left-congruence-Semiring R S)
    ( equivalence-relation-left-congruence-Semiring R T)

refl-relate-same-elements-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : left-congruence-Semiring l2 R) →
  relate-same-elements-left-congruence-Semiring R S S
refl-relate-same-elements-left-congruence-Semiring R S =
  refl-relate-same-elements-equivalence-relation
    ( equivalence-relation-left-congruence-Semiring R S)

is-torsorial-relate-same-elements-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S : left-congruence-Semiring l2 R) →
  is-torsorial (relate-same-elements-left-congruence-Semiring R S)
is-torsorial-relate-same-elements-left-congruence-Semiring R S =
  is-torsorial-Eq-subtype
    ( is-torsorial-relate-same-elements-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-left-congruence-Semiring R S))
    ( is-prop-is-left-congruence-congruence-additive-monoid-Semiring R)
    ( congruence-additive-monoid-left-congruence-Semiring R S)
    ( refl-relate-same-elements-left-congruence-Semiring R S)
    ( is-left-congruence-left-congruence-Semiring R S)

relate-same-elements-eq-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : left-congruence-Semiring l2 R) →
  S ＝ T → relate-same-elements-left-congruence-Semiring R S T
relate-same-elements-eq-left-congruence-Semiring R S .S refl =
  refl-relate-same-elements-left-congruence-Semiring R S

is-equiv-relate-same-elements-eq-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : left-congruence-Semiring l2 R) →
  is-equiv (relate-same-elements-eq-left-congruence-Semiring R S T)
is-equiv-relate-same-elements-eq-left-congruence-Semiring R S =
    fundamental-theorem-id
      ( is-torsorial-relate-same-elements-left-congruence-Semiring R S)
      ( relate-same-elements-eq-left-congruence-Semiring R S)

extensionality-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : left-congruence-Semiring l2 R) →
  (S ＝ T) ≃ relate-same-elements-left-congruence-Semiring R S T
pr1 (extensionality-left-congruence-Semiring R S T) =
  relate-same-elements-eq-left-congruence-Semiring R S T
pr2 (extensionality-left-congruence-Semiring R S T) =
  is-equiv-relate-same-elements-eq-left-congruence-Semiring R S T

eq-relate-same-elements-left-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (S T : left-congruence-Semiring l2 R) →
  relate-same-elements-left-congruence-Semiring R S T → S ＝ T
eq-relate-same-elements-left-congruence-Semiring R S T =
  map-inv-equiv (extensionality-left-congruence-Semiring R S T)
```
