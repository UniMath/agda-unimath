# Higher group actions

```agda
open import foundation.function-extensionality-axiom

module
  higher-group-theory.higher-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types funext
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import higher-group-theory.higher-groups funext
```

</details>

## Idea

An **action of a [higher group](higher-group-theory.higher-groups.md)** `G` on a
type is just a type family over `BG`.

## Definition

```agda
action-∞-Group :
  {l1 : Level} (l2 : Level) (G : ∞-Group l1) → UU (l1 ⊔ lsuc l2)
action-∞-Group l2 G = classifying-type-∞-Group G → UU l2

module _
  {l1 l2 : Level} (G : ∞-Group l1) (X : action-∞-Group l2 G)
  where

  type-action-∞-Group : UU l2
  type-action-∞-Group = X (shape-∞-Group G)

  mul-action-∞-Group :
    type-∞-Group G → type-action-∞-Group → type-action-∞-Group
  mul-action-∞-Group = tr X

  associative-mul-action-∞-Group :
    (h g : type-∞-Group G) (x : type-action-∞-Group) →
    (mul-action-∞-Group (mul-∞-Group G h g) x) ＝
    (mul-action-∞-Group g (mul-action-∞-Group h x))
  associative-mul-action-∞-Group = tr-concat {B = X}

  unit-law-mul-action-∞-Group :
    (x : type-action-∞-Group) → mul-action-∞-Group refl x ＝ x
  unit-law-mul-action-∞-Group x = refl
```
