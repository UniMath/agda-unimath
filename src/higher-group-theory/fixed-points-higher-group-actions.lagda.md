# Fixed points of higher group actions

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.fixed-points-higher-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import higher-group-theory.higher-group-actions funext
open import higher-group-theory.higher-groups funext
```

</details>

## Idea

The type of fixed points of a higher group action `X : BG → UU` is the type of
sections `(u : BG) → X u`.

## Definition

```agda
fixed-point-action-∞-Group :
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G) → UU (l1 ⊔ l2)
fixed-point-action-∞-Group G X = (u : classifying-type-∞-Group G) → X u
```
