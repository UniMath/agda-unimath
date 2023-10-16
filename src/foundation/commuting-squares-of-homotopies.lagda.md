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
      z ------> i
        bottom
```

is said to **commute** if there is a homotopy `left ∙h bottom ~ top ∙h right`.
Such a homotopy is called a **coherence** of the square.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  coherence-square-homotopies :
    (left : f ~ h) (bottom : h ~ i) (top : f ~ g) (right : g ~ i) → UU (l1 ⊔ l2)
  coherence-square-homotopies left bottom top right =
    left ∙h bottom ~ top ∙h right
```
