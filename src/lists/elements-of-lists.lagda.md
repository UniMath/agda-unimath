# Elements of lists

```agda
module lists.elements-of-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

We define {{#concept "elementhood" Agda=element-list}} in
[lists](lists.lists.md).

## Definition

```agda
module _
  {l : Level}
  {A : UU l}
  where

  data element-list : A → list A → UU l where
    is-head-element-list :
      (a : A) (l : list A) → element-list a (cons a l)
    is-in-tail-element-list :
      (a x : A) (l : list A) → element-list a l → element-list a (cons x l)

  infix 6 _∈-list_
  _∈-list_ : A → list A → UU l
  _∈-list_ = element-list
```
