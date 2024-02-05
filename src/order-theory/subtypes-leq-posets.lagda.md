# Subtypes leq Posets

```agda
module order-theory.subtypes-leq-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  subtypes-leq-Preorder : Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 subtypes-leq-Preorder = subtype l2 A
  pr1 (pr2 subtypes-leq-Preorder) = leq-prop-subtype
  pr1 (pr2 (pr2 subtypes-leq-Preorder)) = refl-leq-subtype
  pr2 (pr2 (pr2 subtypes-leq-Preorder)) = transitive-leq-subtype

  subtypes-leq-Poset : Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  pr1 subtypes-leq-Poset = subtypes-leq-Preorder
  pr2 subtypes-leq-Poset = antisymmetric-leq-subtype
```
