# Congruence relations on semirings

```agda
module ring-theory.congruence-relations-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.congruence-relations-monoids

open import ring-theory.semirings
```

</details>

## Idea

A congruence relation on a semiring `R` is a congruence relation on the
underlying additive monoid of `R` which is also a congruence relation on the
multiplicative monoid of `R`.

## Definition

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-congruence-Semiring :
    {l2 : Level}
    (S : congruence-Monoid l2 (additive-monoid-Semiring R)) → UU (l1 ⊔ l2)
  is-congruence-Semiring S =
    is-congruence-Monoid
      ( multiplicative-monoid-Semiring R)
      ( eq-rel-congruence-Monoid (additive-monoid-Semiring R) S)

  is-congruence-eq-rel-Semiring :
    {l2 : Level} (S : Equivalence-Relation l2 (type-Semiring R)) → UU (l1 ⊔ l2)
  is-congruence-eq-rel-Semiring S =
    ( is-congruence-Monoid (additive-monoid-Semiring R) S) ×
    ( is-congruence-Monoid (multiplicative-monoid-Semiring R) S)

congruence-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
congruence-Semiring l2 R =
  Σ ( congruence-Monoid l2 (additive-monoid-Semiring R))
    ( is-congruence-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (S : congruence-Semiring l2 R)
  where

  congruence-additive-monoid-congruence-Semiring :
    congruence-Monoid l2 (additive-monoid-Semiring R)
  congruence-additive-monoid-congruence-Semiring = pr1 S

  eq-rel-congruence-Semiring : Equivalence-Relation l2 (type-Semiring R)
  eq-rel-congruence-Semiring =
    eq-rel-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  prop-congruence-Semiring : Relation-Prop l2 (type-Semiring R)
  prop-congruence-Semiring =
    prop-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  sim-congruence-Semiring : (x y : type-Semiring R) → UU l2
  sim-congruence-Semiring =
    sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  is-prop-sim-congruence-Semiring :
    (x y : type-Semiring R) → is-prop (sim-congruence-Semiring x y)
  is-prop-sim-congruence-Semiring =
    is-prop-sim-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  refl-congruence-Semiring :
    is-reflexive sim-congruence-Semiring
  refl-congruence-Semiring =
    refl-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  symmetric-congruence-Semiring :
    is-symmetric sim-congruence-Semiring
  symmetric-congruence-Semiring =
    symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  equiv-symmetric-congruence-Semiring :
    (x y : type-Semiring R) →
    sim-congruence-Semiring x y ≃ sim-congruence-Semiring y x
  equiv-symmetric-congruence-Semiring =
    equiv-symmetric-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  transitive-congruence-Semiring :
    is-transitive sim-congruence-Semiring
  transitive-congruence-Semiring =
    transitive-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  add-congruence-Semiring :
    is-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( eq-rel-congruence-Semiring)
  add-congruence-Semiring =
    mul-congruence-Monoid
      ( additive-monoid-Semiring R)
      ( congruence-additive-monoid-congruence-Semiring)

  mul-congruence-Semiring :
    is-congruence-Monoid
      ( multiplicative-monoid-Semiring R)
      ( eq-rel-congruence-Semiring)
  mul-congruence-Semiring = pr2 S

construct-congruence-Semiring :
  {l1 l2 : Level} (R : Semiring l1) →
  (S : Equivalence-Relation l2 (type-Semiring R)) →
  is-congruence-Monoid (additive-monoid-Semiring R) S →
  is-congruence-Monoid (multiplicative-monoid-Semiring R) S →
  congruence-Semiring l2 R
pr1 (pr1 (construct-congruence-Semiring R S H K)) = S
pr2 (pr1 (construct-congruence-Semiring R S H K)) = H
pr2 (construct-congruence-Semiring R S H K) = K
```
