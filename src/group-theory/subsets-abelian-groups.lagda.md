# Subsets of abelian groups

```agda
module group-theory.subsets-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.subsets-groups
```

</details>

## Idea

A **subset** of an [abelian group](group-theory.abelian-groups.md) `A` is a
[subtype](foundation.subtypes.md) of the underlying type of `A`.

## Definitions

### Subsets of abelian groups

```agda
subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → UU ((lsuc l) ⊔ l1)
subset-Ab l A = subset-Group l (group-Ab A)

is-set-subset-Ab :
  (l : Level) {l1 : Level} (A : Ab l1) → is-set (subset-Ab l A)
is-set-subset-Ab l A = is-set-subset-Group (group-Ab A)
```
