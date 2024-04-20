# Equivalence relations

```agda
module foundation-core.equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.propositions
```

</details>

## Idea

An equivalence relation is a relation valued in propositions, which is
reflexive,symmetric, and transitive.

## Definition

```agda
is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Relation-Prop R ×
  is-symmetric-Relation-Prop R ×
  is-transitive-Relation-Prop R

equivalence-relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
equivalence-relation l A = Σ (Relation-Prop l A) is-equivalence-relation

prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → Relation-Prop l2 A
prop-equivalence-relation = pr1

sim-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} → equivalence-relation l2 A → A → A → UU l2
sim-equivalence-relation R = type-Relation-Prop (prop-equivalence-relation R)

abstract
  is-prop-sim-equivalence-relation :
    {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (x y : A) →
    is-prop (sim-equivalence-relation R x y)
  is-prop-sim-equivalence-relation R =
    is-prop-type-Relation-Prop (prop-equivalence-relation R)

is-prop-is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  is-prop (is-equivalence-relation R)
is-prop-is-equivalence-relation R =
  is-prop-product
    ( is-prop-is-reflexive-Relation-Prop R)
    ( is-prop-product
      ( is-prop-is-symmetric-Relation-Prop R)
      ( is-prop-is-transitive-Relation-Prop R))

is-equivalence-relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Prop (l1 ⊔ l2)
pr1 (is-equivalence-relation-Prop R) = is-equivalence-relation R
pr2 (is-equivalence-relation-Prop R) = is-prop-is-equivalence-relation R

is-equivalence-relation-prop-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) →
  is-equivalence-relation (prop-equivalence-relation R)
is-equivalence-relation-prop-equivalence-relation R = pr2 R

refl-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-reflexive (sim-equivalence-relation R)
refl-equivalence-relation R =
  pr1 (is-equivalence-relation-prop-equivalence-relation R)

symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) →
  is-symmetric (sim-equivalence-relation R)
symmetric-equivalence-relation R =
  pr1 (pr2 (is-equivalence-relation-prop-equivalence-relation R))

transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) → is-transitive (sim-equivalence-relation R)
transitive-equivalence-relation R =
  pr2 (pr2 (is-equivalence-relation-prop-equivalence-relation R))

inhabited-subtype-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} →
  equivalence-relation l2 A → A → inhabited-subtype l2 A
pr1 (inhabited-subtype-equivalence-relation R x) = prop-equivalence-relation R x
pr2 (inhabited-subtype-equivalence-relation R x) =
  unit-trunc-Prop (x , refl-equivalence-relation R x)
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) {x y : A} →
  sim-equivalence-relation R x y ↔ sim-equivalence-relation R y x
pr1 (iff-symmetric-equivalence-relation R) =
  symmetric-equivalence-relation R _ _
pr2 (iff-symmetric-equivalence-relation R) =
  symmetric-equivalence-relation R _ _

equiv-symmetric-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) {x y : A} →
  sim-equivalence-relation R x y ≃ sim-equivalence-relation R y x
equiv-symmetric-equivalence-relation R =
  equiv-iff'
    ( prop-equivalence-relation R _ _)
    ( prop-equivalence-relation R _ _)
    ( iff-symmetric-equivalence-relation R)
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R x y →
  (sim-equivalence-relation R y z ↔ sim-equivalence-relation R x z)
pr1 (iff-transitive-equivalence-relation R r) s =
  transitive-equivalence-relation R _ _ _ s r
pr2 (iff-transitive-equivalence-relation R r) s =
  transitive-equivalence-relation R _ _ _
    ( s)
    ( symmetric-equivalence-relation R _ _ r)

equiv-transitive-equivalence-relation :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R x y →
  (sim-equivalence-relation R y z ≃ sim-equivalence-relation R x z)
equiv-transitive-equivalence-relation R r =
  equiv-iff'
    ( prop-equivalence-relation R _ _)
    ( prop-equivalence-relation R _ _)
    ( iff-transitive-equivalence-relation R r)
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-transitive-equivalence-relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R y z →
  (sim-equivalence-relation R x y ↔ sim-equivalence-relation R x z)
pr1 (iff-transitive-equivalence-relation' R r) =
  transitive-equivalence-relation R _ _ _ r
pr2 (iff-transitive-equivalence-relation' R r) =
  transitive-equivalence-relation R _ _ _
    ( symmetric-equivalence-relation R _ _ r)

equiv-transitive-equivalence-relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : equivalence-relation l2 A) {x y z : A} →
  sim-equivalence-relation R y z →
  (sim-equivalence-relation R x y ≃ sim-equivalence-relation R x z)
equiv-transitive-equivalence-relation' R r =
  equiv-iff'
    ( prop-equivalence-relation R _ _)
    ( prop-equivalence-relation R _ _)
    ( iff-transitive-equivalence-relation' R r)
```

## Examples

### The indiscrete equivalence relation on a type

```agda
indiscrete-equivalence-relation :
  {l1 : Level} (A : UU l1) → equivalence-relation lzero A
pr1 (indiscrete-equivalence-relation A) x y = unit-Prop
pr1 (pr2 (indiscrete-equivalence-relation A)) _ = star
pr1 (pr2 (pr2 (indiscrete-equivalence-relation A))) _ _ _ = star
pr2 (pr2 (pr2 (indiscrete-equivalence-relation A))) _ _ _ _ _ = star

raise-indiscrete-equivalence-relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → equivalence-relation l2 A
pr1 (raise-indiscrete-equivalence-relation l A) x y = raise-unit-Prop l
pr1 (pr2 (raise-indiscrete-equivalence-relation l A)) _ = raise-star
pr1 (pr2 (pr2 (raise-indiscrete-equivalence-relation l A))) _ _ _ = raise-star
pr2 (pr2 (pr2 (raise-indiscrete-equivalence-relation l A))) _ _ _ _ _ =
  raise-star
```
