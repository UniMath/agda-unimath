# Subsets of semigroups

```agda
module group-theory.subsets-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A **subset of a semigroup** `G` is simply a [subtype](foundation.subtypes.md) of the underlying type of the [semigroup](group-theory.semigroups.md) `G`.

## Definitions

### Subsets of semigroups

```agda
subset-Semigroup :
  {l1 : Level} (l2 : Level) (G : Semigroup l1) → UU (l1 ⊔ lsuc l2)
subset-Semigroup l2 G = subtype l2 (type-Semigroup G)

module _
  {l1 l2 : Level} (G : Semigroup l1) (P : subset-Semigroup l2 G)
  where

  is-in-subset-Semigroup : type-Semigroup G → UU l2
  is-in-subset-Semigroup = is-in-subtype P

  is-closed-under-eq-subset-Semigroup :
    {x y : type-Semigroup G} →
    is-in-subset-Semigroup x → (x ＝ y) → is-in-subset-Semigroup y
  is-closed-under-eq-subset-Semigroup =
    is-closed-under-eq-subtype P

  is-closed-under-eq-subset-Semigroup' :
    {x y : type-Semigroup G} →
    is-in-subset-Semigroup y → (x ＝ y) → is-in-subset-Semigroup x
  is-closed-under-eq-subset-Semigroup' =
    is-closed-under-eq-subtype' P

  is-prop-is-in-subset-Semigroup :
    (x : type-Semigroup G) → is-prop (is-in-subset-Semigroup x)
  is-prop-is-in-subset-Semigroup = is-prop-is-in-subtype P

  type-subset-Semigroup : UU (l1 ⊔ l2)
  type-subset-Semigroup = type-subtype P

  is-set-type-subset-Semigroup : is-set type-subset-Semigroup
  is-set-type-subset-Semigroup =
    is-set-type-subtype P (is-set-type-Semigroup G)

  set-subset-Semigroup : Set (l1 ⊔ l2)
  set-subset-Semigroup = set-subset (set-Semigroup G) P

  inclusion-subset-Semigroup : type-subset-Semigroup → type-Semigroup G
  inclusion-subset-Semigroup = inclusion-subtype P

  ap-inclusion-subset-Semigroup :
    (x y : type-subset-Semigroup) →
    x ＝ y → (inclusion-subset-Semigroup x ＝ inclusion-subset-Semigroup y)
  ap-inclusion-subset-Semigroup = ap-inclusion-subtype P

  is-in-subset-inclusion-subset-Semigroup :
    (x : type-subset-Semigroup) →
    is-in-subset-Semigroup (inclusion-subset-Semigroup x)
  is-in-subset-inclusion-subset-Semigroup =
    is-in-subtype-inclusion-subtype P
```
