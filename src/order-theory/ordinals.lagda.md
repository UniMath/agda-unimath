# Ordinals

```agda
module order-theory.ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.well-founded-orders
open import order-theory.well-founded-relations
```

</details>

## Idea

An ordinal is a propositional relation that is

- Transitive: `R x y` and `R y z` imply `R x y`.
- Extensional: `R x y` and `R y x` imply `x ＝ y`.
- Well-founded: a structure on which it is well-defined to do induction.

In other words, it is a
[well-founded order](order-theory.well-founded-orders.md) that is `Prop`-valued
and antisymmetric.

## Definitions

### The predicate of being an ordinal

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Relation-Prop l2 X)
  where

  is-ordinal : UU (l1 ⊔ l2)
  is-ordinal =
    is-well-founded-order-Relation (type-Relation-Prop R) ×
    is-antisymmetric (type-Relation-Prop R)
```

### Ordinals

```agda
Ordinal : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Ordinal l2 X = Σ (Relation-Prop l2 X) is-ordinal

module _
  {l1 l2 : Level} {X : UU l1} (S : Ordinal l2 X)
  where

  lt-prop-Ordinal : Relation-Prop l2 X
  lt-prop-Ordinal = pr1 S

  lt-Ordinal : Relation l2 X
  lt-Ordinal = type-Relation-Prop lt-prop-Ordinal

  is-ordinal-Ordinal :
    is-ordinal lt-prop-Ordinal
  is-ordinal-Ordinal = pr2 S

  is-well-founded-order-Ordinal :
    is-well-founded-order-Relation lt-Ordinal
  is-well-founded-order-Ordinal = pr1 is-ordinal-Ordinal

  is-antisymmetric-Ordinal :
    is-antisymmetric lt-Ordinal
  is-antisymmetric-Ordinal = pr2 is-ordinal-Ordinal

  is-transitive-Ordinal : is-transitive lt-Ordinal
  is-transitive-Ordinal =
    pr1 is-well-founded-order-Ordinal

  is-well-founded-relation-Ordinal :
    is-well-founded-Relation lt-Ordinal
  is-well-founded-relation-Ordinal =
    pr2 is-well-founded-order-Ordinal

  well-founded-relation-Ordinal : Well-Founded-Relation l2 X
  pr1 well-founded-relation-Ordinal =
    lt-Ordinal
  pr2 well-founded-relation-Ordinal =
    is-well-founded-relation-Ordinal

  is-asymmetric-Ordinal :
    is-asymmetric lt-Ordinal
  is-asymmetric-Ordinal =
    is-asymmetric-Well-Founded-Relation well-founded-relation-Ordinal

  is-irreflexive-Ordinal :
    is-irreflexive lt-Ordinal
  is-irreflexive-Ordinal =
    is-irreflexive-Well-Founded-Relation
      ( well-founded-relation-Ordinal)
```
