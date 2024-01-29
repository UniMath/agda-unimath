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

Given a commuting triangle of identifications

```text
       top
    x ----- y
     \     /
 left \   / right
       \ /
        z     ,
```

we may consider three ways of attaching new identifications to it: prepending
`p : u ＝ x` to the left, which gives us a commuting triangle

```text
         p ∙ top
        u ----- y
         \     /
 p ∙ left \   / right
           \ /
            z     ,
```

or appending an identification `p : z ＝ u` to the right, which gives

```text
           top
        u ----- y
         \     /
 left ∙ p \   / right ∙ p
           \ /
            z     ,
```

or splicing an identification `p : y ＝ u` and its inverse into the middle, to
get

```text
     top ∙ p
    u ----- y
     \     /
 left \   / p⁻¹ ∙ right
       \ /
        z     ,
```

which isn't formalized yet.

Because concatenation of identifications is an equivalence, it follows that all
of these transformations are equivalences.

These lemmas are useful in proofs involving path algebra, because taking
`equiv-right-whisker-triangle-identicications` as an example, it provides us
with two maps: the forward direction states
`(p ＝ q ∙ r) → (p ∙ s ＝ q ∙ (r ∙ s))`, which allows one to append an
identification without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out an identification in parentheses.

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  (left : x ＝ z) (top : x ＝ y) {right : y ＝ z} (p : z ＝ u)
  where

  equiv-right-whisker-triangle-identifications :
    ( coherence-triangle-identifications left right top) ≃
    ( coherence-triangle-identifications (left ∙ p) (right ∙ p) top)
  equiv-right-whisker-triangle-identifications =
    ( equiv-concat-assoc' (left ∙ p) top right p) ∘e
    ( equiv-right-whisker-identification p)

  right-whisker-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top
  right-whisker-triangle-identifications =
    map-equiv equiv-right-whisker-triangle-identifications

  right-unwhisker-triangle-identifications :
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications left right top
  right-unwhisker-triangle-identifications =
    map-inv-equiv equiv-right-whisker-triangle-identifications

  equiv-right-whisker-triangle-identifications' :
    ( coherence-triangle-identifications' left right top) ≃
    ( coherence-triangle-identifications' (left ∙ p) (right ∙ p) top)
  equiv-right-whisker-triangle-identifications' =
    ( equiv-concat-assoc top right p (left ∙ p)) ∘e
    ( equiv-right-whisker-identification p)

  right-whisker-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top
  right-whisker-triangle-identifications' =
    map-equiv equiv-right-whisker-triangle-identifications'

  right-unwhisker-triangle-identifications' :
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications' left right top
  right-unwhisker-triangle-identifications' =
    map-inv-equiv equiv-right-whisker-triangle-identifications'

module _
  {l : Level} {A : UU l} {x y z u : A}
  (p : u ＝ x) {left : x ＝ z} {right : y ＝ z} {top : x ＝ y}
  where

  equiv-left-whisker-triangle-identifications :
    ( coherence-triangle-identifications left right top) ≃
    ( coherence-triangle-identifications (p ∙ left) right (p ∙ top))
  equiv-left-whisker-triangle-identifications =
    ( inv-equiv (equiv-concat-assoc' (p ∙ left) p top right)) ∘e
    ( equiv-left-whisker-identification p)

  left-whisker-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (p ∙ left) right (p ∙ top)
  left-whisker-triangle-identifications =
    map-equiv equiv-left-whisker-triangle-identifications

  left-unwhisker-triangle-identifications :
    coherence-triangle-identifications (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications left right top
  left-unwhisker-triangle-identifications =
    map-inv-equiv equiv-left-whisker-triangle-identifications

  equiv-left-whisker-triangle-identifications' :
    ( coherence-triangle-identifications' left right top) ≃
    ( coherence-triangle-identifications' (p ∙ left) right (p ∙ top))
  equiv-left-whisker-triangle-identifications' =
    ( inv-equiv (equiv-concat-assoc p top right (p ∙ left))) ∘e
    ( equiv-left-whisker-identification p)

  left-whisker-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top)
  left-whisker-triangle-identifications' =
    map-equiv equiv-left-whisker-triangle-identifications'

  left-unwhisker-triangle-identifications' :
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications' left right top
  left-unwhisker-triangle-identifications' =
    map-inv-equiv equiv-left-whisker-triangle-identifications'
```
