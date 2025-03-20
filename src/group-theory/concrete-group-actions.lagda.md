# Concrete group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.concrete-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types funext
open import foundation.sets funext
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.concrete-groups funext
```

</details>

## Idea

Given a [concrete group](group-theory.concrete-groups.md) `G`, a **concrete
action of** `G` on a type is defined to be a type family over `BG`. Given a type
family `X` over `BG`, the type being acted on is the type `X *`, and the action
of `G` on `X *` is given by transport.

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1)
  where

  action-Concrete-Group : UU (l1 ⊔ lsuc l2)
  action-Concrete-Group = classifying-type-Concrete-Group G → Set l2

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G)
  where

  set-action-Concrete-Group : Set l2
  set-action-Concrete-Group = X (shape-Concrete-Group G)

  type-action-Concrete-Group : UU l2
  type-action-Concrete-Group = type-Set set-action-Concrete-Group

  is-set-type-action-Concrete-Group : is-set type-action-Concrete-Group
  is-set-type-action-Concrete-Group = is-set-type-Set set-action-Concrete-Group

  mul-action-Concrete-Group :
    type-Concrete-Group G →
    type-action-Concrete-Group → type-action-Concrete-Group
  mul-action-Concrete-Group g x = tr (type-Set ∘ X) g x
```
