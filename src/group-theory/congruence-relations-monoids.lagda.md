# Congruence relations on monoids

```agda
module group-theory.congruence-relations-monoids where
```

<details><summary>Imports</summary>

```agda
open import group-theory.congruence-relations-semigroups
open import group-theory.monoids
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A congruence relation on a monoid `G` is an equivalence relation `≡` on `G` such that for every `x1 x2 y1 y2 : G` such that `x1 ≡ x2` and `y1 ≡ y2` we have `x1 · y1 ≡ x2 · y2`.

## Definition

```agda
is-congruence-Eq-Rel-Monoid :
  {l1 l2 : Level} (M : Monoid l1) → Eq-Rel l2 (type-Monoid M) → UU (l1 ⊔ l2)
is-congruence-Eq-Rel-Monoid M R =
  is-congruence-Eq-Rel-Semigroup (semigroup-Monoid M) R

congruence-Monoid : {l : Level} (l2 : Level) (M : Monoid l) → UU (l ⊔ lsuc l2)
congruence-Monoid l2 M =
  Σ (Eq-Rel l2 (type-Monoid M)) (is-congruence-Eq-Rel-Monoid M)

module _
  {l1 l2 : Level} (M : Monoid l1) (R : congruence-Monoid l2 M)
  where

  eq-rel-congruence-Monoid : Eq-Rel l2 (type-Monoid M)
  eq-rel-congruence-Monoid = pr1 R

  prop-congruence-Monoid : Rel-Prop l2 (type-Monoid M)
  prop-congruence-Monoid = prop-Eq-Rel eq-rel-congruence-Monoid

  sim-congruence-Monoid : (x y : type-Monoid M) → UU l2
  sim-congruence-Monoid = sim-Eq-Rel eq-rel-congruence-Monoid

  is-prop-sim-congruence-Monoid :
    (x y : type-Monoid M) → is-prop (sim-congruence-Monoid x y)
  is-prop-sim-congruence-Monoid = is-prop-sim-Eq-Rel eq-rel-congruence-Monoid

  refl-congruence-Monoid : is-reflexive-Rel-Prop prop-congruence-Monoid
  refl-congruence-Monoid = refl-Eq-Rel eq-rel-congruence-Monoid

  symm-congruence-Monoid : is-symmetric-Rel-Prop prop-congruence-Monoid
  symm-congruence-Monoid = symm-Eq-Rel eq-rel-congruence-Monoid

  equiv-symm-congruence-Monoid :
    (x y : type-Monoid M) → sim-congruence-Monoid x y ≃ sim-congruence-Monoid y x
  equiv-symm-congruence-Monoid x y = equiv-symm-Eq-Rel eq-rel-congruence-Monoid

  trans-congruence-Monoid : is-transitive-Rel-Prop prop-congruence-Monoid
  trans-congruence-Monoid = trans-Eq-Rel eq-rel-congruence-Monoid

  mul-congruence-Monoid : is-congruence-Eq-Rel-Monoid M eq-rel-congruence-Monoid
  mul-congruence-Monoid = pr2 R
```
