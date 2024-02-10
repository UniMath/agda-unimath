# Commuting squares of homotopies

```agda
module foundation-core.commuting-squares-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-identifications
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

is said to be a {{#concept "commuting square" Disambiguation="homotopies"}} of
homotopies if there is a homotopy `left ∙h bottom ~ top ∙h right `. Such a
homotopy is called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-homotopies}}
of the square.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (f : A) → B f}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  coherence-square-homotopies : UU (l1 ⊔ l2)
  coherence-square-homotopies =
    left ∙h bottom ~ top ∙h right

  coherence-square-homotopies' : UU (l1 ⊔ l2)
  coherence-square-homotopies' =
    top ∙h right ~ left ∙h bottom
```

### Inverting squares of homotopies horizontally

Given a commuting square of homotopies

```text
           top
       f -------> g
       |          |
  left |          | right
       ∨          ∨
       h -------> i,
          bottom
```

the square of homotopies

```text
             inv top
        g ------------> f
        |               |
  right |               | left
        ∨               ∨
        i ------------> h
           inv bottom
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  horizontal-inv-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies (inv-htpy top) right left (inv-htpy bottom)
  horizontal-inv-coherence-square-homotopies top left right bottom = {!   !}
```

### Inverting squares of homotopies vertically

Given a commuting square of homotopies

```text
           top
       f -------> g
       |          |
  left |          | right
       ∨          ∨
       h -------> i,
          bottom
```

the square of homotopies

```text
              bottom
           h -------> i
           |          |
  inv left |          | inv right
           ∨          ∨
           f -------> g
               top
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  vertical-inv-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies bottom (inv-htpy left) (inv-htpy right) top
  vertical-inv-coherence-square-homotopies top left right bottom H x =
    {! vertical-inv-coherence-square-identifications (top x) (left x) (right x) (bottom x) (H x)  !}
```
