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

Eq-Relation :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Eq-Relation l A = Σ (Relation-Prop l A) is-equivalence-relation

prop-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} → Eq-Relation l2 A → Relation-Prop l2 A
prop-Eq-Relation = pr1

sim-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} → Eq-Relation l2 A → A → A → UU l2
sim-Eq-Relation R = type-Relation-Prop (prop-Eq-Relation R)

abstract
  is-prop-sim-Eq-Relation :
    {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) (x y : A) →
    is-prop (sim-Eq-Relation R x y)
  is-prop-sim-Eq-Relation R = is-prop-type-Relation-Prop (prop-Eq-Relation R)

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

is-equivalence-relation-prop-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) →
  is-equivalence-relation (prop-Eq-Relation R)
is-equivalence-relation-prop-Eq-Relation R = pr2 R

refl-Eq-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Eq-Relation l2 A) → is-reflexive (sim-Eq-Relation R)
refl-Eq-Relation R = pr1 (is-equivalence-relation-prop-Eq-Relation R)

symmetric-Eq-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Eq-Relation l2 A) → is-symmetric (sim-Eq-Relation R)
symmetric-Eq-Relation R = pr1 (pr2 (is-equivalence-relation-prop-Eq-Relation R))

transitive-Eq-Relation :
  {l1 l2 : Level} {A : UU l1}
  (R : Eq-Relation l2 A) → is-transitive (sim-Eq-Relation R)
transitive-Eq-Relation R =
  pr2 (pr2 (is-equivalence-relation-prop-Eq-Relation R))

inhabited-subtype-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} → Eq-Relation l2 A → A → inhabited-subtype l2 A
pr1 (inhabited-subtype-Eq-Relation R x) = prop-Eq-Relation R x
pr2 (inhabited-subtype-Eq-Relation R x) =
  unit-trunc-Prop (x , refl-Eq-Relation R x)
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symmetric-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y : A} →
  sim-Eq-Relation R x y ↔ sim-Eq-Relation R y x
pr1 (iff-symmetric-Eq-Relation R) = symmetric-Eq-Relation R _ _
pr2 (iff-symmetric-Eq-Relation R) = symmetric-Eq-Relation R _ _

equiv-symmetric-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y : A} →
  sim-Eq-Relation R x y ≃ sim-Eq-Relation R y x
equiv-symmetric-Eq-Relation R =
  equiv-iff'
    ( prop-Eq-Relation R _ _)
    ( prop-Eq-Relation R _ _)
    ( iff-symmetric-Eq-Relation R)
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-transitive-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y z : A} →
  sim-Eq-Relation R x y → (sim-Eq-Relation R y z ↔ sim-Eq-Relation R x z)
pr1 (iff-transitive-Eq-Relation R r) s = transitive-Eq-Relation R _ _ _ s r
pr2 (iff-transitive-Eq-Relation R r) s =
  transitive-Eq-Relation R _ _ _ s (symmetric-Eq-Relation R _ _ r)

equiv-transitive-Eq-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y z : A} →
  sim-Eq-Relation R x y → (sim-Eq-Relation R y z ≃ sim-Eq-Relation R x z)
equiv-transitive-Eq-Relation R r =
  equiv-iff'
    ( prop-Eq-Relation R _ _)
    ( prop-Eq-Relation R _ _)
    ( iff-transitive-Eq-Relation R r)
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-transitive-Eq-Relation' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y z : A} →
  sim-Eq-Relation R y z → (sim-Eq-Relation R x y ↔ sim-Eq-Relation R x z)
pr1 (iff-transitive-Eq-Relation' R r) s = transitive-Eq-Relation R _ _ _ r s
pr2 (iff-transitive-Eq-Relation' R r) s =
  transitive-Eq-Relation R _ _ _ (symmetric-Eq-Relation R _ _ r) s

equiv-transitive-Eq-Relation' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A) {x y z : A} →
  sim-Eq-Relation R y z → (sim-Eq-Relation R x y ≃ sim-Eq-Relation R x z)
equiv-transitive-Eq-Relation' R r =
  equiv-iff'
    ( prop-Eq-Relation R _ _)
    ( prop-Eq-Relation R _ _)
    ( iff-transitive-Eq-Relation' R r)
```

## Examples

### The indiscrete equivalence relation on a type

```agda
indiscrete-Eq-Relation :
  {l1 : Level} (A : UU l1) → Eq-Relation lzero A
pr1 (indiscrete-Eq-Relation A) x y = unit-Prop
pr1 (pr2 (indiscrete-Eq-Relation A)) _ = star
pr1 (pr2 (pr2 (indiscrete-Eq-Relation A))) _ _ _ = star
pr2 (pr2 (pr2 (indiscrete-Eq-Relation A))) _ _ _ _ _ = star

raise-indiscrete-Eq-Relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → Eq-Relation l2 A
pr1 (raise-indiscrete-Eq-Relation l A) x y = raise-unit-Prop l
pr1 (pr2 (raise-indiscrete-Eq-Relation l A)) _ = raise-star
pr1 (pr2 (pr2 (raise-indiscrete-Eq-Relation l A))) _ _ _ = raise-star
pr2 (pr2 (pr2 (raise-indiscrete-Eq-Relation l A))) _ _ _ _ _ = raise-star
```
