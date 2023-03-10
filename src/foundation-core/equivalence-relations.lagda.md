# Equivalence relations

```agda
module foundation-core.equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Idea

An equivalence relation is a relation valued in propositions, which is reflexive,symmetric, and transitive.

## Definition

```agda
is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → UU (l1 ⊔ l2)
is-equivalence-relation R =
  is-reflexive-Rel-Prop R ×
    ( is-symmetric-Rel-Prop R × is-transitive-Rel-Prop R)

Eq-Rel :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Eq-Rel l A = Σ (Rel-Prop l A) is-equivalence-relation

prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → Rel-Prop l2 A
prop-Eq-Rel = pr1

sim-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → A → A → UU l2
sim-Eq-Rel R = type-Rel-Prop (prop-Eq-Rel R)

abstract
  is-prop-sim-Eq-Rel :
    {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (x y : A) →
    is-prop (sim-Eq-Rel R x y)
  is-prop-sim-Eq-Rel R = is-prop-type-Rel-Prop (prop-Eq-Rel R)

is-prop-is-equivalence-relation :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  is-prop (is-equivalence-relation R)
is-prop-is-equivalence-relation R =
  is-prop-prod
    ( is-prop-is-reflexive-Rel-Prop R)
    ( is-prop-prod
      ( is-prop-is-symmetric-Rel-Prop R)
      ( is-prop-is-transitive-Rel-Prop R))

is-equivalence-relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → Prop (l1 ⊔ l2)
pr1 (is-equivalence-relation-Prop R) = is-equivalence-relation R
pr2 (is-equivalence-relation-Prop R) = is-prop-is-equivalence-relation R

is-equivalence-relation-prop-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-equivalence-relation (prop-Eq-Rel R)
is-equivalence-relation-prop-Eq-Rel R = pr2 R

refl-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-reflexive-Rel-Prop (prop-Eq-Rel R)
refl-Eq-Rel R = pr1 (is-equivalence-relation-prop-Eq-Rel R)

symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-symmetric-Rel-Prop (prop-Eq-Rel R)
symm-Eq-Rel R = pr1 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) →
  is-transitive-Rel-Prop (prop-Eq-Rel R)
trans-Eq-Rel R = pr2 (pr2 (is-equivalence-relation-prop-Eq-Rel R))

inhabited-subtype-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} → Eq-Rel l2 A → A → inhabited-subtype l2 A
pr1 (inhabited-subtype-Eq-Rel R x) = prop-Eq-Rel R x
pr2 (inhabited-subtype-Eq-Rel R x) = unit-trunc-Prop (pair x (refl-Eq-Rel R))
```

## Properties

### Symmetry induces equivalences `R(x,y) ≃ R(y,x)`

```agda
iff-symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  sim-Eq-Rel R x y ↔ sim-Eq-Rel R y x
pr1 (iff-symm-Eq-Rel R) = symm-Eq-Rel R
pr2 (iff-symm-Eq-Rel R) = symm-Eq-Rel R

equiv-symm-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y : A} →
  sim-Eq-Rel R x y ≃ sim-Eq-Rel R y x
equiv-symm-Eq-Rel R =
  equiv-iff' (prop-Eq-Rel R _ _) (prop-Eq-Rel R _ _) (iff-symm-Eq-Rel R)
```

### Transitivity induces equivalences `R(y,z) ≃ R(x,z)`

```agda
iff-trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y z : A} →
  sim-Eq-Rel R x y → (sim-Eq-Rel R y z ↔ sim-Eq-Rel R x z)
pr1 (iff-trans-Eq-Rel R r) s = trans-Eq-Rel R r s
pr2 (iff-trans-Eq-Rel R r) s = trans-Eq-Rel R (symm-Eq-Rel R r) s

equiv-trans-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y z : A} →
  sim-Eq-Rel R x y → (sim-Eq-Rel R y z ≃ sim-Eq-Rel R x z)
equiv-trans-Eq-Rel R r =
  equiv-iff' (prop-Eq-Rel R _ _) (prop-Eq-Rel R _ _) (iff-trans-Eq-Rel R r)
```

### Transitivity induces equivalences `R(x,y) ≃ R(x,z)`

```agda
iff-trans-Eq-Rel' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y z : A} →
  sim-Eq-Rel R y z → (sim-Eq-Rel R x y ↔ sim-Eq-Rel R x z)
pr1 (iff-trans-Eq-Rel' R r) s = trans-Eq-Rel R s r
pr2 (iff-trans-Eq-Rel' R r) s = trans-Eq-Rel R s (symm-Eq-Rel R r)

equiv-trans-Eq-Rel' :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) {x y z : A} →
  sim-Eq-Rel R y z → (sim-Eq-Rel R x y ≃ sim-Eq-Rel R x z)
equiv-trans-Eq-Rel' R r =
  equiv-iff' (prop-Eq-Rel R _ _) (prop-Eq-Rel R _ _) (iff-trans-Eq-Rel' R r)
```
