# Transitive group actions

```agda
module group-theory.transitive-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

A group `G` is said to act transitively on a set `X` if for every `x` and `y` in
`X` there is a group element `g` such that `gx = y`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  is-transitive-Abstract-Group-Action : Prop (l1 ⊔ l2)
  is-transitive-Abstract-Group-Action =
    Π-Prop
      ( type-Abstract-Group-Action G X)
      ( λ x →
        Π-Prop
          ( type-Abstract-Group-Action G X)
          ( λ y →
            ∃-Prop
              ( type-Group G)
              ( λ g → Id (mul-Abstract-Group-Action G X g x) y)))
```
