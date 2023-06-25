# Equivalence relations

```agda
module foundation-core.equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.logical-equivalences
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
    ( is-symmetric-Relation-Prop R × is-transitive-Relation-Prop R)

Equivalence-Relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Equivalence-Relation l A = Σ (Relation-Prop l A) is-equivalence-relation

prop-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} → Equivalence-Relation l2 A → Relation-Prop l2 A
prop-Equivalence-Relation = pr1

sim-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} → Equivalence-Relation l2 A → A → A → UU l2
sim-Equivalence-Relation R = type-Relation-Prop (prop-Equivalence-Relation R)

abstract
  is-prop-sim-Equivalence-Relation :
    {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A) (x y : A) →
    is-prop (sim-Equivalence-Relation R x y)
  is-prop-sim-Equivalence-Relation R =
    is-prop-type-Relation-Prop (prop-Equivalence-Relation R)

is-prop-is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  is-prop (is-equivalence-relation R)
is-prop-is-equivalence-relation R =
  is-prop-prod
    ( is-prop-is-reflexive-Relation-Prop R)
    ( is-prop-prod
      ( is-prop-is-symmetric-Relation-Prop R)
      ( is-prop-is-transitive-Relation-Prop R))

is-equivalence-relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Prop (l1 ⊔ l2)
pr1 (is-equivalence-relation-Prop R) = is-equivalence-relation R
pr2 (is-equivalence-relation-Prop R) = is-prop-is-equivalence-relation R

is-equivalence-relation-prop-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A) →
  is-equivalence-relation (prop-Equivalence-Relation R)
is-equivalence-relation-prop-Equivalence-Relation R = pr2 R

refl-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) →
  is-reflexive (sim-Equivalence-Relation R)
refl-Equivalence-Relation R =
  pr1 (is-equivalence-relation-prop-Equivalence-Relation R)

symmetric-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) →
  is-symmetric (sim-Equivalence-Relation R)
symmetric-Equivalence-Relation R =
  pr1 (pr2 (is-equivalence-relation-prop-Equivalence-Relation R))

transitive-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) → is-transitive (sim-Equivalence-Relation R)
transitive-Equivalence-Relation R =
  pr2 (pr2 (is-equivalence-relation-prop-Equivalence-Relation R))

inhabited-subtype-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} →
  Equivalence-Relation l2 A → A → inhabited-subtype l2 A
pr1 (inhabited-subtype-Equivalence-Relation R x) = prop-Equivalence-Relation R x
pr2 (inhabited-subtype-Equivalence-Relation R x) =
  unit-trunc-Prop (x , refl-Equivalence-Relation R x)
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symmetric-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A) {x y : A} →
  sim-Equivalence-Relation R x y ↔ sim-Equivalence-Relation R y x
pr1 (iff-symmetric-Equivalence-Relation R) =
  symmetric-Equivalence-Relation R _ _
pr2 (iff-symmetric-Equivalence-Relation R) =
  symmetric-Equivalence-Relation R _ _

equiv-symmetric-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A) {x y : A} →
  sim-Equivalence-Relation R x y ≃ sim-Equivalence-Relation R y x
equiv-symmetric-Equivalence-Relation R =
  equiv-iff'
    ( prop-Equivalence-Relation R _ _)
    ( prop-Equivalence-Relation R _ _)
    ( iff-symmetric-Equivalence-Relation R)
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-transitive-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) {x y z : A} →
  sim-Equivalence-Relation R x y →
  (sim-Equivalence-Relation R y z ↔ sim-Equivalence-Relation R x z)
pr1 (iff-transitive-Equivalence-Relation R r) s =
  transitive-Equivalence-Relation R _ _ _ s r
pr2 (iff-transitive-Equivalence-Relation R r) s =
  transitive-Equivalence-Relation R _ _ _
    ( s)
    ( symmetric-Equivalence-Relation R _ _ r)

equiv-transitive-Equivalence-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) {x y z : A} →
  sim-Equivalence-Relation R x y →
  (sim-Equivalence-Relation R y z ≃ sim-Equivalence-Relation R x z)
equiv-transitive-Equivalence-Relation R r =
  equiv-iff'
    ( prop-Equivalence-Relation R _ _)
    ( prop-Equivalence-Relation R _ _)
    ( iff-transitive-Equivalence-Relation R r)
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-transitive-Equivalence-Relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) {x y z : A} →
  sim-Equivalence-Relation R y z →
  (sim-Equivalence-Relation R x y ↔ sim-Equivalence-Relation R x z)
pr1 (iff-transitive-Equivalence-Relation' R r) =
  transitive-Equivalence-Relation R _ _ _ r
pr2 (iff-transitive-Equivalence-Relation' R r) =
  transitive-Equivalence-Relation R _ _ _
    ( symmetric-Equivalence-Relation R _ _ r)

equiv-transitive-Equivalence-Relation' :
  {l1 l2 : Level} {A : UU l1}
  (R : Equivalence-Relation l2 A) {x y z : A} →
  sim-Equivalence-Relation R y z →
  (sim-Equivalence-Relation R x y ≃ sim-Equivalence-Relation R x z)
equiv-transitive-Equivalence-Relation' R r =
  equiv-iff'
    ( prop-Equivalence-Relation R _ _)
    ( prop-Equivalence-Relation R _ _)
    ( iff-transitive-Equivalence-Relation' R r)
```

## Examples

### The indiscrete equivalence relation on a type

```agda
indiscrete-Equivalence-Relation :
  {l1 : Level} (A : UU l1) → Equivalence-Relation lzero A
pr1 (indiscrete-Equivalence-Relation A) x y = unit-Prop
pr1 (pr2 (indiscrete-Equivalence-Relation A)) _ = star
pr1 (pr2 (pr2 (indiscrete-Equivalence-Relation A))) _ _ _ = star
pr2 (pr2 (pr2 (indiscrete-Equivalence-Relation A))) _ _ _ _ _ = star

raise-indiscrete-Equivalence-Relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → Equivalence-Relation l2 A
pr1 (raise-indiscrete-Equivalence-Relation l A) x y = raise-unit-Prop l
pr1 (pr2 (raise-indiscrete-Equivalence-Relation l A)) _ = raise-star
pr1 (pr2 (pr2 (raise-indiscrete-Equivalence-Relation l A))) _ _ _ = raise-star
pr2 (pr2 (pr2 (raise-indiscrete-Equivalence-Relation l A))) _ _ _ _ _ =
  raise-star
```
