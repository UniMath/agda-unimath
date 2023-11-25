# Transitive group actions

```agda
module group-theory.transitive-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

A [group](group-theory.groups.md) `G` is said to **act transitively** on a
[set](foundation-core.sets.md) `X` if for every `x : X` the map

```text
  g ↦ gx : G → X
```

is [surjective](foundation.surjective-maps.md). In other words, a
[group action](group-theory.group-actions.md) is transitive if any two elements
are in the same [orbit](group-theory.orbits-group-actions.md).

## Definitions

### The predicate of being a transitive `G`-set

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  is-transitive-prop-action-Group : Prop (l1 ⊔ l2)
  is-transitive-prop-action-Group =
    Π-Prop
      ( type-action-Group G X)
      ( λ x → is-surjective-Prop (λ g → mul-action-Group G X g x))

  is-transitive-action-Group : UU (l1 ⊔ l2)
  is-transitive-action-Group = type-Prop is-transitive-prop-action-Group

  is-prop-is-transitive-action-Group : is-prop is-transitive-action-Group
  is-prop-is-transitive-action-Group =
    is-prop-type-Prop is-transitive-prop-action-Group
```

## External links

- [transitive action](https://ncatlab.org/nlab/show/transitive+action) at $n$Lab
- [Transitivity properties of group actions](https://en.wikipedia.org/wiki/Group_action#Transitivity_properties)
  at Wikipedia
- [Transitive Group Action](https://mathworld.wolfram.com/TransitiveGroupAction.html)
  at Wolfram MathWorld
- [Transitive group action](https://groupprops.subwiki.org/wiki/Transitive_group_action)
  at Groupprops
