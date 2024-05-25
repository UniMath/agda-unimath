# Transitive Closures

```agda
module foundation.binary-relations-transitive-closures where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  data transitive-closure (R : Relation l2 A) : Relation (l1 ⊔ l2) A
    where
    transitive-closure-base : {x y : A} → R x y → transitive-closure R x y
    transitive-closure-step :
      {x y z : A} → R x y → transitive-closure R y z → transitive-closure R x z

  is-transitive-transitive-closure :
    (R : Relation l2 A) → is-transitive (transitive-closure R)
  is-transitive-transitive-closure
    R x y z c-yz (transitive-closure-base r-xy) =
      transitive-closure-step r-xy c-yz
  is-transitive-transitive-closure
    R x y z c-yz (transitive-closure-step {y = u} r-xu c-uy) =
      transitive-closure-step r-xu
        ( is-transitive-transitive-closure R u y z c-yz c-uy)

  transitive-closure-preserves-reflexivity :
    (R : Relation l2 A) →
    is-reflexive R →
    is-reflexive (transitive-closure R)
  transitive-closure-preserves-reflexivity R is-refl x =
    transitive-closure-base (is-refl x)

  transitive-closure-preserves-symmetry :
    (R : Relation l2 A) →
    is-symmetric R →
    is-symmetric (transitive-closure R)
  transitive-closure-preserves-symmetry R is-sym x y
    (transitive-closure-base r) =
      transitive-closure-base (is-sym x y r)
  transitive-closure-preserves-symmetry
    R is-sym x y (transitive-closure-step {y = u} r-xu c-uy) =
      is-transitive-transitive-closure R y u x
        ( transitive-closure-base (is-sym x u r-xu))
        ( transitive-closure-preserves-symmetry R is-sym u y c-uy)
```

### Transitive closure of a relation valued in propositions

```agda
  transitive-closure-Prop :
    (R : Relation-Prop l2 A) → Relation-Prop (l1 ⊔ l2) A
  transitive-closure-Prop R x y =
    trunc-Prop (transitive-closure (type-Relation-Prop R) x y)

  is-transitive-transitive-closure-Prop :
    (R : Relation-Prop l2 A) →
    is-transitive-Relation-Prop (transitive-closure-Prop R)
  is-transitive-transitive-closure-Prop R x y z c-yz c-xy =
    apply-twice-universal-property-trunc-Prop
      ( c-yz)
      ( c-xy)
      ( transitive-closure-Prop R x z)
      ( λ r-yz r-xy →
        unit-trunc-Prop
          ( is-transitive-transitive-closure
            ( type-Relation-Prop R)
            ( x)
            ( y)
            ( z)
            ( r-yz)
            ( r-xy)))

  transitive-closure-Prop-preserves-reflexivity :
    (R : Relation-Prop l2 A) →
    is-reflexive-Relation-Prop R →
    is-reflexive-Relation-Prop (transitive-closure-Prop R)
  transitive-closure-Prop-preserves-reflexivity R is-refl x =
    unit-trunc-Prop
      ( transitive-closure-preserves-reflexivity
        ( type-Relation-Prop R)
        ( is-refl)
        ( x))

  transitive-closure-Prop-preserves-symmetry :
    (R : Relation-Prop l2 A) →
    is-symmetric-Relation-Prop R →
    is-symmetric-Relation-Prop (transitive-closure-Prop R)
  transitive-closure-Prop-preserves-symmetry R is-sym x y =
    map-universal-property-trunc-Prop
      ( transitive-closure-Prop R y x)
      ( λ r-xy →
        unit-trunc-Prop
          ( transitive-closure-preserves-symmetry
            ( type-Relation-Prop R)
            ( is-sym)
            ( x)
            ( y)
            ( r-xy)))
```
