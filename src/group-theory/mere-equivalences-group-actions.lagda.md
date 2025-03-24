# Mere equivalences of group actions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.mere-equivalences-group-actions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import group-theory.equivalences-group-actions funext univalence truncations
open import group-theory.group-actions funext univalence truncations
open import group-theory.groups funext univalence truncations
```

</details>

## Idea

A **mere equivalence** of [group actions](group-theory.group-actions.md) is an
element of the
[propositional truncation](foundation.propositional-truncations.md) of the type
of [equivalences of group actions](group-theory.equivalences-group-actions.md).

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  mere-equiv-prop-action-Group : Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-prop-action-Group = trunc-Prop (equiv-action-Group G X Y)

  mere-equiv-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-action-Group = type-Prop mere-equiv-prop-action-Group
```
