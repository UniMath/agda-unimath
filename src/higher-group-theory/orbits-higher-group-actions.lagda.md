# Orbits of higher group actions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory.orbits-higher-group-actions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions funext univalence truncations
open import higher-group-theory.higher-groups funext univalence truncations
```

</details>

## Idea

The type of orbits of a higher group action `X` acted upon by `G` is the total
space of `X`.

## Definition

```agda
orbit-action-∞-Group :
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G) → UU (l1 ⊔ l2)
orbit-action-∞-Group G X = Σ (classifying-type-∞-Group G) X
```
