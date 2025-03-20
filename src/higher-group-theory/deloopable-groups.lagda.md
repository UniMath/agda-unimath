# Deloopable groups

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.deloopable-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.groups funext

open import higher-group-theory.deloopable-h-spaces funext
```

</details>

## Idea

A {{#concept "delooping" Disambiguation="group" Agda=delooping-Group}} of a
[group](group-theory.groups.md) `G` is a
[delooping](higher-group-theory.deloopable-h-spaces.md) of the underlying
[H-space](structured-types.h-spaces.md) of `G`. In other words, a delooping of a
group `G` consists of a [higher group](higher-group-theory.higher-groups.md)
`H`, which is defined to be a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type, equipped with an
[equivalence of H-spaces](structured-types.equivalences-h-spaces.md)
`G ≃ h-space-∞-Group H` from `G` to the underlying H-space of `H`.

## Definitions

### Deloopings of groups of a given universe level

```agda
module _
  {l1 : Level} (l2 : Level) (G : Group l1)
  where

  delooping-Group-Level : UU (l1 ⊔ lsuc l2)
  delooping-Group-Level = delooping-H-Space-Level l2 (h-space-Group G)
```

### Deloopings of groups

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  delooping-Group : UU (lsuc l1)
  delooping-Group = delooping-Group-Level l1 G
```

## See also

- [Eilenberg-Mac Lane spaces](higher-group-theory.eilenberg-mac-lane-spaces.md)
