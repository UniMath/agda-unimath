# Subsets of large semigroups

```agda
module group-theory.subsets-large-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.subsets-cumulative-large-sets
open import foundation.universe-levels

open import group-theory.large-semigroups
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a large semigroup" Agda=subset-Large-Semigroup}}
of a [large semigroup](group-theory.large-semigroups.md) is a
[subset](foundation.subsets-cumulative-large-sets.md) of the
[cumulative large set](foundation.cumulative-large-sets.md) of the large
semigroup.

## Definition

```agda
subset-Large-Semigroup :
  {α : Level → Level} {β : Level → Level → Level} →
  (Level → Level) → Large-Semigroup α β → UUω
subset-Large-Semigroup γ G =
  Subset-Cumulative-Large-Set γ (cumulative-large-set-Large-Semigroup G)

module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  (S : subset-Large-Semigroup γ G)
  where

  type-subset-Large-Semigroup : (l : Level) → UU (α l ⊔ γ l)
  type-subset-Large-Semigroup = type-Subset-Cumulative-Large-Set S

  inclusion-subset-Large-Semigroup :
    {l : Level} → type-subset-Large-Semigroup l → type-Large-Semigroup G l
  inclusion-subset-Large-Semigroup = inclusion-Subset-Cumulative-Large-Set S

  is-in-subset-Large-Semigroup :
    {l : Level} → type-Large-Semigroup G l → UU (γ l)
  is-in-subset-Large-Semigroup =
    is-in-Subset-Cumulative-Large-Set S

  prop-is-in-subset-Large-Semigroup :
    {l : Level} → type-Large-Semigroup G l → Prop (γ l)
  prop-is-in-subset-Large-Semigroup =
    prop-is-in-Subset-Cumulative-Large-Set S

  cumulative-large-set-subset-Large-Semigroup :
    Cumulative-Large-Set (λ l → α l ⊔ γ l) β
  cumulative-large-set-subset-Large-Semigroup =
    cumulative-large-set-Subset-Cumulative-Large-Set S

  abstract
    eq-type-subset-Large-Semigroup :
      {l : Level} {x y : type-subset-Large-Semigroup l} →
      inclusion-subset-Large-Semigroup x ＝ inclusion-subset-Large-Semigroup y →
      x ＝ y
    eq-type-subset-Large-Semigroup = eq-type-Subset-Cumulative-Large-Set S

    is-closed-under-raise-subset-Large-Semigroup :
      {l1 : Level} (l2 : Level) (x : type-Large-Semigroup G l1) →
      is-in-subset-Large-Semigroup x →
      is-in-subset-Large-Semigroup (raise-Large-Semigroup G l2 x)
    is-closed-under-raise-subset-Large-Semigroup =
      is-closed-under-raise-Subset-Cumulative-Large-Set S

  sim-preserving-map-inclusion-subset-Large-Semigroup :
    sim-preserving-map-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-subset-Large-Semigroup)
      ( cumulative-large-set-Large-Semigroup G)
  sim-preserving-map-inclusion-subset-Large-Semigroup =
    sim-preserving-map-inclusion-Subset-Cumulative-Large-Set S
```

## Properties

### The property of being closed under multiplication

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (G : Large-Semigroup α β)
  (S : subset-Large-Semigroup γ G)
  where

  is-closed-under-mul-subset-Large-Semigroup : UUω
  is-closed-under-mul-subset-Large-Semigroup =
    {l1 l2 : Level}
    (x : type-Large-Semigroup G l1) (y : type-Large-Semigroup G l2) →
    is-in-subset-Large-Semigroup G S x → is-in-subset-Large-Semigroup G S y →
    is-in-subset-Large-Semigroup G S (mul-Large-Semigroup G x y)
```
