# Free concrete group actions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.free-concrete-group-actions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.function-types funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext univalence truncations
open import group-theory.concrete-groups funext univalence truncations

open import higher-group-theory.free-higher-group-actions funext univalence truncations
```

</details>

## Idea

Consider a [concrete group](group-theory.concrete-groups.md) `G` and a
[concrete group action](group-theory.concrete-group-actions.md) of `G` on `X`.
We say that `X` is **free** if its type of
[orbits](group-theory.orbits-concrete-group-actions.md) is a
[set](foundation.sets.md).

[Equivalently](foundation.logical-equivalences.md), we say that `X` is
**abstractly free** if for any element `x : X (sh G)` of the underlying type of
`X` the action map

```text
  g ↦ mul-action-Concrete-Group G X g x
```

is an [embedding](foundation.embeddings.md).

## Definition

### The predicate of being a free concrete group action

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-free-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-free-prop-action-Concrete-Group =
    is-free-prop-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)

  is-free-action-Concrete-Group : UU (l1 ⊔ l2)
  is-free-action-Concrete-Group =
    is-free-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)

  is-prop-is-free-action-Concrete-Group : is-prop is-free-action-Concrete-Group
  is-prop-is-free-action-Concrete-Group =
    is-prop-is-free-action-∞-Group (∞-group-Concrete-Group G) (type-Set ∘ X)
```

### The predicate of being an abstractly free concrete group action

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-abstractly-free-prop-action-Concrete-Group : Prop (l1 ⊔ l2)
  is-abstractly-free-prop-action-Concrete-Group =
    is-abstractly-free-prop-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-abstractly-free-action-Concrete-Group : UU (l1 ⊔ l2)
  is-abstractly-free-action-Concrete-Group =
    is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-prop-is-abstractly-free-action-Concrete-Group :
    is-prop is-abstractly-free-action-Concrete-Group
  is-prop-is-abstractly-free-action-Concrete-Group =
    is-prop-is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)
```

### Free concrete group actions

```agda
free-action-Concrete-Group :
  {l1 : Level} (l2 : Level) → Concrete-Group l1 → UU (l1 ⊔ lsuc l2)
free-action-Concrete-Group l2 G =
  Σ (action-Concrete-Group l2 G) (is-free-action-Concrete-Group G)
```

## Properties

### A concrete group action is free if and only if it is abstractly free

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  is-abstractly-free-is-free-action-Concrete-Group :
    is-free-action-Concrete-Group G X →
    is-abstractly-free-action-Concrete-Group G X
  is-abstractly-free-is-free-action-Concrete-Group =
    is-abstractly-free-is-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)

  is-free-is-abstractly-free-action-Concrete-Group :
    is-abstractly-free-action-Concrete-Group G X →
    is-free-action-Concrete-Group G X
  is-free-is-abstractly-free-action-Concrete-Group =
    is-free-is-abstractly-free-action-∞-Group
      ( ∞-group-Concrete-Group G)
      ( type-Set ∘ X)
```
