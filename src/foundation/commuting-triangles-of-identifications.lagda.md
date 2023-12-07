# Commuting triangles of identifications

```agda
module foundation.commuting-triangles-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.path-algebra
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A triangle of [identifications](foundation-core.identity-types.md)

```text
 x ----- y
  \     /
   \   /
    \ /
     z
```

is said to **commute** if there is a higher identification between the `x ＝ z`
and the concatenated identification `x ＝ y ＝ z`.

## Definition

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  coherence-triangle-identifications :
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) → UU l
  coherence-triangle-identifications left right top = left ＝ (top ∙ right)

  coherence-triangle-identifications' :
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) → UU l
  coherence-triangle-identifications' left right top = (top ∙ right) ＝ left
```

## Properties

### Whiskering of triangles of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  (left : x ＝ z) (top : x ＝ y) {right : y ＝ z} (p : z ＝ u)
  where

  equiv-right-whisk-triangle-identifications :
    ( coherence-triangle-identifications left right top) ≃
    ( coherence-triangle-identifications (left ∙ p) (right ∙ p) top)
  equiv-right-whisk-triangle-identifications =
    ( equiv-concat-assoc' (left ∙ p) top right p) ∘e
    ( equiv-identification-right-whisk p)

  right-whisk-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top
  right-whisk-triangle-identifications =
    map-equiv equiv-right-whisk-triangle-identifications

  right-unwhisk-triangle-identifications :
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications left right top
  right-unwhisk-triangle-identifications =
    map-inv-equiv equiv-right-whisk-triangle-identifications

  equiv-right-whisk-triangle-identifications' :
    ( coherence-triangle-identifications' left right top) ≃
    ( coherence-triangle-identifications' (left ∙ p) (right ∙ p) top)
  equiv-right-whisk-triangle-identifications' =
    ( equiv-concat-assoc top right p (left ∙ p)) ∘e
    ( equiv-identification-right-whisk p)

  right-whisk-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top
  right-whisk-triangle-identifications' =
    map-equiv equiv-right-whisk-triangle-identifications'

  right-unwhisk-triangle-identifications' :
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications' left right top
  right-unwhisk-triangle-identifications' =
    map-inv-equiv equiv-right-whisk-triangle-identifications'

module _
  {l : Level} {A : UU l} {x y z u : A}
  (p : u ＝ x) {left : x ＝ z} {right : y ＝ z} {top : x ＝ y}
  where

  equiv-left-whisk-triangle-identifications :
    ( coherence-triangle-identifications left right top) ≃
    ( coherence-triangle-identifications (p ∙ left) right (p ∙ top))
  equiv-left-whisk-triangle-identifications =
    ( inv-equiv (equiv-concat-assoc' (p ∙ left) p top right)) ∘e
    ( equiv-identification-left-whisk p)

  left-whisk-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (p ∙ left) right (p ∙ top)
  left-whisk-triangle-identifications =
    map-equiv equiv-left-whisk-triangle-identifications

  left-unwhisk-triangle-identifications :
    coherence-triangle-identifications (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications left right top
  left-unwhisk-triangle-identifications =
    map-inv-equiv equiv-left-whisk-triangle-identifications

  equiv-left-whisk-triangle-identifications' :
    ( coherence-triangle-identifications' left right top) ≃
    ( coherence-triangle-identifications' (p ∙ left) right (p ∙ top))
  equiv-left-whisk-triangle-identifications' =
    ( inv-equiv (equiv-concat-assoc p top right (p ∙ left))) ∘e
    ( equiv-identification-left-whisk p)

  left-whisk-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top)
  left-whisk-triangle-identifications' =
    map-equiv equiv-left-whisk-triangle-identifications'

  left-unwhisk-triangle-identifications' :
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications' left right top
  left-unwhisk-triangle-identifications' =
    map-inv-equiv equiv-left-whisk-triangle-identifications'
```
