# Orbits of concrete group actions

```agda
module group-theory.orbits-concrete-group-actions where
```

<details><summary>Imports</summary>
```agda
open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.sets
open import foundation.universe-levels
```
</details>

## Definition

```agda
orbit-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  UU (l1 ⊔ l2)
orbit-action-Concrete-Group G X =
  Σ (classifying-type-Concrete-Group G) (type-Set ∘ X)
```
