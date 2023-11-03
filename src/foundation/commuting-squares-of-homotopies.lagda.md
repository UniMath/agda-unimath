# Commuting squares of homotopies

```agda
module foundation.commuting-squares-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.homotopies
```

</details>

## Idea

A square of [homotopies](foundation-core.homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      v         v
      h ------> i
        bottom
```

is said to **commute** if there is a homotopy `top ∙h right ~ left ∙h bottom`.
Such a homotopy is called a **coherence** of the square.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) → UU (l1 ⊔ l2)
  coherence-square-homotopies top left right bottom =
    left ∙h bottom ~ top ∙h right
```
