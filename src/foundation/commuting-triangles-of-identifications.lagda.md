# Commuting triangles of identifications

```agda
module foundation.commuting-triangles-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A triangle of [identifications](foundation-core.identity-types.md)

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

is said to **commute** if there is a higher identification between the `x ＝ z`
and the concatenated identification `x ＝ y ＝ z`.

## Definitions

### Commuting triangles of identifications

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
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z     ,
```

we may consider three ways of attaching new identifications to it:

1. Prepending `p : u ＝ x` to the left gives us a commuting triangle

   ```text
             p ∙ top
            u ----> y
             \     /
     p ∙ left \   / right
               ∨ ∨
                z.
   ```

   In other words, we have a map

   ```text
     (left ＝ top ∙ right) → (p ∙ left ＝ (p ∙ top) ∙ right).
   ```

2. Appending an identification `p : z ＝ u` to the right gives a commuting
   triangle of identifications

   ```text
               top
            x ----> y
             \     /
     left ∙ p \   / right ∙ p
               ∨ ∨
                u.
   ```

   In other words, we have a map

   ```text
     (left ＝ top ∙ right) → (left ∙ p ＝ top ∙ (right ∙ p)).

   ```

3. Splicing an identification `p : y ＝ u` and its inverse into the middle gives
   a commuting triangle of identifications

   ```text
         top ∙ p
        x ----> u
         \     /
     left \   / p⁻¹ ∙ right
           ∨ ∨
            z.
   ```

   In other words, we have a map

   ```text
     (left ＝ top ∙ right) → left ＝ (top ∙ p) ∙ (p⁻¹ ∙ right).
   ```

   Similarly, we have a map

   ```text
     (left ＝ top ∙ right) → left ＝ (top ∙ p⁻¹) ∙ (p ∙ right).
   ```

   This isn't formalized yet.

Because concatenation of identifications is an equivalence, it follows that all
of these transformations are equivalences.

These operations are useful in proofs involving path algebra, because taking
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

### The action of functions on commuting triangles of identifications

Consider a commuting triangle of identifications

```text
        top
     x ----> y
      \     /
  left \   / right
        ∨ ∨
         z
```

in a type `A` and consider a map `f : A → B`. Then we obtain a commuting
triangle of identifications

```text
          ap f top
        f x ----> f y
           \     /
  ap f left \   / ap f right
             ∨ ∨
             f z
```

Furthermore, in the case where the identification `right` is `refl` we obtain an identification

```text
  inv right-unit ＝
  map-coherence-triangle-identifications p refl p (inv right-unit)
```

and in the case where the identification `top` is refl` we obtain

```text
  refl ＝ map-coherence-triangle-identifications p p refl refl.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-coherence-triangle-identifications :
    {x y z : A} (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (ap f left) (ap f right) (ap f top)
  map-coherence-triangle-identifications .(top ∙ right) right top refl =
    ap-concat f top right

  compute-refl-right-map-coherence-triangle-identifications :
    {x y : A} (p : x ＝ y) →
    inv right-unit ＝
    map-coherence-triangle-identifications p refl p (inv right-unit)
  compute-refl-right-map-coherence-triangle-identifications refl = refl

  compute-refl-top-map-coherence-triangle-identifications :
    {x  y : A} (p : x ＝ y) →
    refl ＝ map-coherence-triangle-identifications p p refl refl
  compute-refl-top-map-coherence-triangle-identifications p = refl
```
