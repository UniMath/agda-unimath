# Mere equivalences of group actions

```agda
module group-theory.mere-equivalences-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.equivalences-group-actions
open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Definition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : Abstract-Group-Action G l2)
  (Y : Abstract-Group-Action G l3)
  where

  mere-equiv-Abstract-Group-Action-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action-Prop =
    trunc-Prop (equiv-Abstract-Group-Action G X Y)

  mere-equiv-Abstract-Group-Action : UU (l1 ⊔ l2 ⊔ l3)
  mere-equiv-Abstract-Group-Action =
    type-Prop mere-equiv-Abstract-Group-Action-Prop
```
