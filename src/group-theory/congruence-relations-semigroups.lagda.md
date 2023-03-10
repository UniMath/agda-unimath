# Congruence relations on semigroups

```agda
module group-theory.congruence-relations-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A congruence relation on a semigroup `G` is an equivalence relation `≡` on `G` such that for every `x1 x2 y1 y2 : G` such that `x1 ≡ x2` and `y1 ≡ y2` we have `x1 · y1 ≡ x2 · y2`.

## Definition

```agda
is-congruence-Semigroup-Prop :
  {l1 l2 : Level} (G : Semigroup l1) →
  Eq-Rel l2 (type-Semigroup G) → Prop (l1 ⊔ l2)
is-congruence-Semigroup-Prop G R =
  Π-Prop'
    ( type-Semigroup G)
    ( λ x1 →
      Π-Prop'
        ( type-Semigroup G)
        ( λ x2 →
          Π-Prop'
            ( type-Semigroup G)
            ( λ y1 →
              Π-Prop'
                ( type-Semigroup G)
                ( λ y2 →
                  function-Prop
                    ( sim-Eq-Rel R x1 x2)
                    ( function-Prop
                      ( sim-Eq-Rel R y1 y2)
                      ( prop-Eq-Rel R
                        ( mul-Semigroup G x1 y1)
                        ( mul-Semigroup G x2 y2)))))))

is-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) →
  Eq-Rel l2 (type-Semigroup G) → UU (l1 ⊔ l2)
is-congruence-Semigroup G R =
  type-Prop (is-congruence-Semigroup-Prop G R)

is-prop-is-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R : Eq-Rel l2 (type-Semigroup G)) →
  is-prop (is-congruence-Semigroup G R)
is-prop-is-congruence-Semigroup G R =
  is-prop-type-Prop (is-congruence-Semigroup-Prop G R)

congruence-Semigroup :
  {l : Level} (l2 : Level) (G : Semigroup l) → UU (l ⊔ lsuc l2)
congruence-Semigroup l2 G =
  Σ (Eq-Rel l2 (type-Semigroup G)) (is-congruence-Semigroup G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (R : congruence-Semigroup l2 G)
  where

  eq-rel-congruence-Semigroup : Eq-Rel l2 (type-Semigroup G)
  eq-rel-congruence-Semigroup = pr1 R

  prop-congruence-Semigroup : Rel-Prop l2 (type-Semigroup G)
  prop-congruence-Semigroup = prop-Eq-Rel eq-rel-congruence-Semigroup

  sim-congruence-Semigroup : (x y : type-Semigroup G) → UU l2
  sim-congruence-Semigroup = sim-Eq-Rel eq-rel-congruence-Semigroup

  is-prop-sim-congruence-Semigroup :
    (x y : type-Semigroup G) → is-prop (sim-congruence-Semigroup x y)
  is-prop-sim-congruence-Semigroup =
    is-prop-sim-Eq-Rel eq-rel-congruence-Semigroup

  refl-congruence-Semigroup : is-reflexive-Rel-Prop prop-congruence-Semigroup
  refl-congruence-Semigroup = refl-Eq-Rel eq-rel-congruence-Semigroup

  symm-congruence-Semigroup : is-symmetric-Rel-Prop prop-congruence-Semigroup
  symm-congruence-Semigroup = symm-Eq-Rel eq-rel-congruence-Semigroup

  equiv-symm-congruence-Semigroup :
    (x y : type-Semigroup G) →
    sim-congruence-Semigroup x y ≃ sim-congruence-Semigroup y x
  equiv-symm-congruence-Semigroup x y =
    equiv-symm-Eq-Rel eq-rel-congruence-Semigroup

  trans-congruence-Semigroup : is-transitive-Rel-Prop prop-congruence-Semigroup
  trans-congruence-Semigroup = trans-Eq-Rel eq-rel-congruence-Semigroup

  mul-congruence-Semigroup :
    is-congruence-Semigroup G eq-rel-congruence-Semigroup
  mul-congruence-Semigroup = pr2 R
```

## Properties

### Characterizing equality of congruences of semigroups

```agda
relate-same-elements-congruence-Semigroup :
  {l1 l2 l3 : Level} (G : Semigroup l1) →
  congruence-Semigroup l2 G → congruence-Semigroup l3 G → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-congruence-Semigroup G R S =
  relate-same-elements-Eq-Rel
    ( eq-rel-congruence-Semigroup G R)
    ( eq-rel-congruence-Semigroup G S)

refl-relate-same-elements-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R : congruence-Semigroup l2 G) →
  relate-same-elements-congruence-Semigroup G R R
refl-relate-same-elements-congruence-Semigroup G R =
  refl-relate-same-elements-Eq-Rel (eq-rel-congruence-Semigroup G R)

is-contr-total-relate-same-elements-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R : congruence-Semigroup l2 G) →
  is-contr
    ( Σ ( congruence-Semigroup l2 G)
        ( relate-same-elements-congruence-Semigroup G R))
is-contr-total-relate-same-elements-congruence-Semigroup G R =
  is-contr-total-Eq-subtype
    ( is-contr-total-relate-same-elements-Eq-Rel
      ( eq-rel-congruence-Semigroup G R))
    ( is-prop-is-congruence-Semigroup G)
    ( eq-rel-congruence-Semigroup G R)
    ( refl-relate-same-elements-congruence-Semigroup G R)
    ( mul-congruence-Semigroup G R)

relate-same-elements-eq-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R S : congruence-Semigroup l2 G) →
  R ＝ S → relate-same-elements-congruence-Semigroup G R S
relate-same-elements-eq-congruence-Semigroup G R .R refl =
  refl-relate-same-elements-congruence-Semigroup G R

is-equiv-relate-same-elements-eq-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R S : congruence-Semigroup l2 G) →
  is-equiv (relate-same-elements-eq-congruence-Semigroup G R S)
is-equiv-relate-same-elements-eq-congruence-Semigroup G R =
  fundamental-theorem-id
    ( is-contr-total-relate-same-elements-congruence-Semigroup G R)
    ( relate-same-elements-eq-congruence-Semigroup G R)

extensionality-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R S : congruence-Semigroup l2 G) →
  (R ＝ S) ≃ relate-same-elements-congruence-Semigroup G R S
pr1 (extensionality-congruence-Semigroup G R S) =
  relate-same-elements-eq-congruence-Semigroup G R S
pr2 (extensionality-congruence-Semigroup G R S) =
  is-equiv-relate-same-elements-eq-congruence-Semigroup G R S

eq-relate-same-elements-congruence-Semigroup :
  {l1 l2 : Level} (G : Semigroup l1) (R S : congruence-Semigroup l2 G) →
  relate-same-elements-congruence-Semigroup G R S → R ＝ S
eq-relate-same-elements-congruence-Semigroup G R S =
  map-inv-equiv (extensionality-congruence-Semigroup G R S)
```
