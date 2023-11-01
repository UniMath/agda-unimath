# Commuting pentagons of identifications

```agda
module foundation.commuting-pentagons-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A pentagon of [identifications](foundation-core.identity-types.md)

```text
             top
           x --- y
top-left  /       \ top-right
         /         \
        z           w
          \       /
bottom-left \   / bottom-right
              v
```

is said to **commute** if there is an identification

```text
  top-left ∙ bottom-left ＝ (top ∙ top-right) ∙ bottom-right.
```

Such an identification is called a **coherence** of the pentagon.

## Definition

```agda
module _
  {l : Level} {A : UU l} {x y z w v : A}
  where

  coherence-pentagon-identifications :
    (top : x ＝ y)
    (top-left : x ＝ z) (top-right : y ＝ w)
    (bottom-left : z ＝ v) (bottom-right : w ＝ v) → UU l
  coherence-pentagon-identifications
    top top-left top-right bottom-left bottom-right =
    top-left ∙ bottom-left ＝ (top ∙ top-right) ∙ bottom-right
```
