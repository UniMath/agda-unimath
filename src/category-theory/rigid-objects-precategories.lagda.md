# Rigid objects in a precategory

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.rigid-objects-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.universe-levels
```

</details>

## Idea

A **rigid object** in a [precategory](category-theory.precategories.md) is an
object whose [automorphism group](group-theory.automorphism-groups.md) is
[trivial](group-theory.trivial-groups.md).

## Definitions

### The predicate of being rigid

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (x : obj-Precategory C)
  where

  is-rigid-obj-prop-Precategory : Prop l2
  is-rigid-obj-prop-Precategory = is-contr-Prop (iso-Precategory C x x)

  is-rigid-obj-Precategory : UU l2
  is-rigid-obj-Precategory = type-Prop is-rigid-obj-prop-Precategory

  is-prop-is-rigid-obj-Precategory : is-prop is-rigid-obj-Precategory
  is-prop-is-rigid-obj-Precategory =
    is-prop-type-Prop is-rigid-obj-prop-Precategory
```

### The type of rigid objects in a precategory

```agda
rigid-obj-Precategory : {l1 l2 : Level} (C : Precategory l1 l2) → UU (l1 ⊔ l2)
rigid-obj-Precategory C = Σ (obj-Precategory C) (is-rigid-obj-Precategory C)

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  obj-rigid-obj-Precategory : rigid-obj-Precategory C → obj-Precategory C
  obj-rigid-obj-Precategory = pr1

  is-rigid-rigid-obj-Precategory :
    (x : rigid-obj-Precategory C) →
    is-rigid-obj-Precategory C (obj-rigid-obj-Precategory x)
  is-rigid-rigid-obj-Precategory = pr2
```

## External links

- [rigid object](https://ncatlab.org/nlab/show/rigid+object) at $n$Lab
