# Commuting triangles of identifications

```agda
module foundation.commuting-triangles-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import foundation-core.commuting-squares-of-identifications
open import foundation-core.equivalences
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

is said to **commute** if there is an identification `p ＝ q ∙ r`.

## Definitions

### Commuting triangles of identifications

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  coherence-triangle-identifications :
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) → UU l
  coherence-triangle-identifications left right top = (left ＝ top ∙ right)

  coherence-triangle-identifications' :
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) → UU l
  coherence-triangle-identifications' left right top = (top ∙ right ＝ left)
```

### The horizontally constant triangle of identifications

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  horizontal-refl-coherence-triangle-identifications :
    (p : x ＝ y) → coherence-triangle-identifications p p refl
  horizontal-refl-coherence-triangle-identifications p = refl
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
         z,
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

Because concatenation of identifications is an
[equivalence](foundation-core.equivalences.md), it follows that all of these
transformations are equivalences.

These operations are useful in proofs involving
[path algebra](foundation.path-algebra.md), because taking
`equiv-right-whisker-triangle-identifications` as an example, it provides us
with two maps: the forward direction states
`(p ＝ q ∙ r) → (p ∙ s ＝ q ∙ (r ∙ s))`, which allows one to append an
identification without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out an identification in parentheses.

#### Left whiskering commuting squares of identifications

There is an equivalence of commuting squares

```text
        top                        p ∙ top
     x ----> y                    u ----> y
      \     /                      \     /
  left \   / right    ≃    p ∙ left \   / right
        ∨ ∨                          ∨ ∨
         z                            z
```

for any identification `p : u ＝ x`.

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  (p : u ＝ x) (left : x ＝ z) (right : y ＝ z) (top : x ＝ y)
  where

  equiv-left-whisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications left right top ≃
    coherence-triangle-identifications (p ∙ left) right (p ∙ top)
  equiv-left-whisker-concat-coherence-triangle-identifications =
    ( equiv-inv-concat' _ (assoc p top right)) ∘e
    ( equiv-left-whisker-concat p)

  left-whisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (p ∙ left) right (p ∙ top)
  left-whisker-concat-coherence-triangle-identifications =
    map-equiv equiv-left-whisker-concat-coherence-triangle-identifications

  left-unwhisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications left right top
  left-unwhisker-concat-coherence-triangle-identifications =
    map-inv-equiv equiv-left-whisker-concat-coherence-triangle-identifications

  is-equiv-left-whisker-concat-coherence-triangle-identifications :
    is-equiv
      ( left-whisker-concat-coherence-triangle-identifications)
  is-equiv-left-whisker-concat-coherence-triangle-identifications =
    is-equiv-map-equiv
      equiv-left-whisker-concat-coherence-triangle-identifications

  equiv-left-whisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' left right top ≃
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top)
  equiv-left-whisker-concat-coherence-triangle-identifications' =
    ( equiv-concat (assoc p top right) _) ∘e
    ( equiv-left-whisker-concat p)

  left-whisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top)
  left-whisker-concat-coherence-triangle-identifications' =
    map-equiv equiv-left-whisker-concat-coherence-triangle-identifications'

  left-unwhisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' (p ∙ left) right (p ∙ top) →
    coherence-triangle-identifications' left right top
  left-unwhisker-concat-coherence-triangle-identifications' =
    map-inv-equiv equiv-left-whisker-concat-coherence-triangle-identifications'

  is-equiv-left-whisker-concat-coherence-triangle-identifications' :
    is-equiv left-whisker-concat-coherence-triangle-identifications'
  is-equiv-left-whisker-concat-coherence-triangle-identifications' =
    is-equiv-map-equiv
      equiv-left-whisker-concat-coherence-triangle-identifications'
```

#### Right whiskering commuting squares of identifications

There is an equivalence of commuting triangles of identifications

```text
        top                            top
     x ----> y                      x ----> y
      \     /                        \     /
  left \   / right     ≃     left ∙ p \   / right ∙ p
        ∨ ∨                            ∨ ∨
         z                              u
```

for any identification `p : z ＝ u`.

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) (p : z ＝ u)
  where

  equiv-right-whisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications left right top ≃
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top
  equiv-right-whisker-concat-coherence-triangle-identifications =
    ( equiv-concat-assoc' (left ∙ p) top right p) ∘e
    ( equiv-right-whisker-concat p)

  right-whisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top
  right-whisker-concat-coherence-triangle-identifications =
    map-equiv equiv-right-whisker-concat-coherence-triangle-identifications

  right-unwhisker-concat-coherence-triangle-identifications :
    coherence-triangle-identifications (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications left right top
  right-unwhisker-concat-coherence-triangle-identifications =
    map-inv-equiv equiv-right-whisker-concat-coherence-triangle-identifications

  is-equiv-right-whisker-concat-coherence-triangle-identifications :
    is-equiv right-whisker-concat-coherence-triangle-identifications
  is-equiv-right-whisker-concat-coherence-triangle-identifications =
    is-equiv-map-equiv
      equiv-right-whisker-concat-coherence-triangle-identifications

  equiv-right-whisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' left right top ≃
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top
  equiv-right-whisker-concat-coherence-triangle-identifications' =
    ( equiv-concat-assoc top right p (left ∙ p)) ∘e
    ( equiv-right-whisker-concat p)

  right-whisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top
  right-whisker-concat-coherence-triangle-identifications' =
    map-equiv equiv-right-whisker-concat-coherence-triangle-identifications'

  right-unwhisker-concat-coherence-triangle-identifications' :
    coherence-triangle-identifications' (left ∙ p) (right ∙ p) top →
    coherence-triangle-identifications' left right top
  right-unwhisker-concat-coherence-triangle-identifications' =
    map-inv-equiv equiv-right-whisker-concat-coherence-triangle-identifications'

  is-equiv-right-whisker-concat-coherence-triangle-identifications' :
    is-equiv right-whisker-concat-coherence-triangle-identifications'
  is-equiv-right-whisker-concat-coherence-triangle-identifications' =
    is-equiv-map-equiv
      equiv-right-whisker-concat-coherence-triangle-identifications'
```

#### Splicing a pair of mutual inverse identifications in a commuting triangle of identifications

Consider two identifications `p : y ＝ u` and `q : u ＝ y` equipped with an
identification `α : inv p ＝ q`. Then we have an equivalence of commuting
triangles of identifications

```text
        top                       top ∙ p
     x ----> y                   x ----> u
      \     /                     \     /
  left \   / right     ≃     left  \   / q ∙ right
        ∨ ∨                         ∨ ∨
         z                           z.
```

Note that we have formulated the equivalence in such a way that it gives us both
equivalences

```text
  (left ＝ top ∙ right) ≃ (left ＝ (top ∙ p) ∙ (p⁻¹ ∙ right)),
```

and

```text
  (left ＝ top ∙ right) ≃ (left ＝ (top ∙ p⁻¹) ∙ (p ∙ right))
```

without further ado.

```agda
module _
  {l : Level} {A : UU l} {x y z u : A}
  where

  equiv-splice-coherence-triangle-identifications :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left right top ≃
    coherence-triangle-identifications left (q ∙ right) (top ∙ p)
  equiv-splice-coherence-triangle-identifications refl .refl refl
    left right top =
    equiv-concat' left (right-whisker-concat (inv right-unit) right)

  splice-coherence-triangle-identifications :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications left (q ∙ right) (top ∙ p)
  splice-coherence-triangle-identifications refl .refl refl
    left right top t =
    t ∙ inv (right-whisker-concat right-unit right)

  unsplice-coherence-triangle-identifications :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left (q ∙ right) (top ∙ p) →
    coherence-triangle-identifications left right top
  unsplice-coherence-triangle-identifications refl .refl refl
    left right top t =
    t ∙ right-whisker-concat right-unit right

  equiv-splice-coherence-triangle-identifications' :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications' left right top ≃
    coherence-triangle-identifications' left (q ∙ right) (top ∙ p)
  equiv-splice-coherence-triangle-identifications' refl .refl refl
    left right top =
    equiv-concat (right-whisker-concat right-unit right) left

  splice-coherence-triangle-identifications' :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications' left right top →
    coherence-triangle-identifications' left (q ∙ right) (top ∙ p)
  splice-coherence-triangle-identifications' refl .refl refl
    left right top t =
    right-whisker-concat right-unit right ∙ t

  unsplice-coherence-triangle-identifications' :
    (p : y ＝ u) (q : u ＝ y) (α : inv p ＝ q) →
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications' left (q ∙ right) (top ∙ p) →
    coherence-triangle-identifications' left right top
  unsplice-coherence-triangle-identifications' refl .refl refl
    left right top t =
    inv (right-whisker-concat right-unit right) ∙ t
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

Furthermore, in the case where the identification `right` is `refl` we obtain an
identification

```text
  inv right-unit ＝
  map-coherence-triangle-identifications p refl p (inv right-unit)
```

and in the case where the identification `top` is `refl` we obtain

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
    {x y : A} (p : x ＝ y) →
    refl ＝ map-coherence-triangle-identifications p p refl refl
  compute-refl-top-map-coherence-triangle-identifications p = refl
```

### Inverting one side of a commuting triangle of identifications

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  transpose-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : b ＝ a)
    {top' : a ＝ b} (α : inv top ＝ top') →
    coherence-triangle-identifications right left top →
    coherence-triangle-identifications left right top'
  transpose-top-coherence-triangle-identifications left right top refl t =
    left-transpose-eq-concat _ _ _ (inv t)

  equiv-transpose-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : b ＝ a) →
    coherence-triangle-identifications right left top ≃
    coherence-triangle-identifications left right (inv top)
  equiv-transpose-top-coherence-triangle-identifications left right top =
    equiv-left-transpose-eq-concat _ _ _ ∘e equiv-inv _ _

  equiv-higher-transpose-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : b ＝ a)
    {left' : a ＝ c} (p : left ＝ left')
    {top' : a ＝ b} (α : inv top ＝ top') →
    (s : coherence-triangle-identifications right left top) →
    (t : coherence-triangle-identifications right left' top) →
    coherence-triangle-identifications t (left-whisker-concat top p) s ≃
    coherence-triangle-identifications
      ( transpose-top-coherence-triangle-identifications left right top α s)
      ( transpose-top-coherence-triangle-identifications left' right top α t)
      ( p)
  equiv-higher-transpose-top-coherence-triangle-identifications
    left right top refl refl s t =
    ( equiv-ap
      ( equiv-transpose-top-coherence-triangle-identifications left right top)
      ( _)
      ( _)) ∘e
    ( equiv-inv _ _) ∘e
    ( equiv-concat' _ right-unit)

  higher-transpose-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : b ＝ a) →
    {left' : a ＝ c} (p : left ＝ left')
    {top' : a ＝ b} (q : inv top ＝ top') →
    (s : coherence-triangle-identifications right left top) →
    (t : coherence-triangle-identifications right left' top) →
    coherence-triangle-identifications t (left-whisker-concat top p) s →
    coherence-triangle-identifications
      ( transpose-top-coherence-triangle-identifications left right top q s)
      ( transpose-top-coherence-triangle-identifications left' right top q t)
      ( p)
  higher-transpose-top-coherence-triangle-identifications
    left right top p q s t =
    map-equiv
      ( equiv-higher-transpose-top-coherence-triangle-identifications
        left right top p q s t)

  transpose-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : c ＝ b) (top : a ＝ b)
    {right' : b ＝ c} (p : inv right ＝ right') →
    coherence-triangle-identifications top right left →
    coherence-triangle-identifications left right' top
  transpose-right-coherence-triangle-identifications left right top refl t =
    right-transpose-eq-concat _ _ _ (inv t)

  equiv-transpose-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : c ＝ b) (top : a ＝ b) →
    coherence-triangle-identifications top right left ≃
    coherence-triangle-identifications left (inv right) top
  equiv-transpose-right-coherence-triangle-identifications left right top =
    equiv-right-transpose-eq-concat _ _ _ ∘e equiv-inv _ _

  equiv-higher-transpose-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : c ＝ b) (top : a ＝ b) →
    {left' : a ＝ c} (p : left ＝ left')
    {right' : b ＝ c} (q : inv right ＝ right') →
    (s : coherence-triangle-identifications top right left) →
    (t : coherence-triangle-identifications top right left') →
    coherence-triangle-identifications t (right-whisker-concat p right) s ≃
    coherence-triangle-identifications
      ( transpose-right-coherence-triangle-identifications left right top q s)
      ( transpose-right-coherence-triangle-identifications left' right top q t)
      ( p)
  equiv-higher-transpose-right-coherence-triangle-identifications
    left right top refl refl s t =
    ( equiv-ap
      ( equiv-transpose-right-coherence-triangle-identifications left right top)
      ( _)
      ( _)) ∘e
    ( equiv-inv _ _) ∘e
    ( equiv-concat' t right-unit)

  higher-transpose-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : c ＝ b) (top : a ＝ b) →
    {left' : a ＝ c} (p : left ＝ left')
    {right' : b ＝ c} (q : inv right ＝ right') →
    (s : coherence-triangle-identifications top right left) →
    (t : coherence-triangle-identifications top right left') →
    coherence-triangle-identifications t (right-whisker-concat p right) s →
    coherence-triangle-identifications
      ( transpose-right-coherence-triangle-identifications left right top q s)
      ( transpose-right-coherence-triangle-identifications left' right top q t)
      ( p)
  higher-transpose-right-coherence-triangle-identifications
    left right top p q s t =
    map-equiv
      ( equiv-higher-transpose-right-coherence-triangle-identifications
        ( left)
        ( right)
        ( top)
        ( p)
        ( q)
        ( s)
        ( t))
```

### Inverting all sides of a commuting triangle of identifications

```agda
module _
  {l1 : Level} {A : UU l1} {x y z : A}
  where

  inv-coherence-triangle-identifications :
    (left : x ＝ z) (right : y ＝ z) (top : x ＝ y) →
    coherence-triangle-identifications left right top →
    coherence-triangle-identifications (inv left) (inv top) (inv right)
  inv-coherence-triangle-identifications .(top ∙ right) right top refl =
    distributive-inv-concat top right
```

### Concatenating identifications on edges with coherences of commuting triangles of identifications

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  equiv-concat-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {top' : a ＝ b} (p : top' ＝ top) →
    coherence-triangle-identifications left right top' ≃
    coherence-triangle-identifications left right top
  equiv-concat-top-coherence-triangle-identifications left right top p =
    equiv-concat' left (right-whisker-concat p right)

  concat-top-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {top' : a ＝ b} (p : top' ＝ top) →
    coherence-triangle-identifications left right top' →
    coherence-triangle-identifications left right top
  concat-top-coherence-triangle-identifications left right top p =
    map-equiv
      ( equiv-concat-top-coherence-triangle-identifications left right top p)

  equiv-concat-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {right' : b ＝ c} (p : right' ＝ right) →
    coherence-triangle-identifications left right' top ≃
    coherence-triangle-identifications left right top
  equiv-concat-right-coherence-triangle-identifications left right top p =
    equiv-concat' left (left-whisker-concat top p)

  concat-right-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {right' : b ＝ c} (p : right' ＝ right) →
    coherence-triangle-identifications left right' top →
    coherence-triangle-identifications left right top
  concat-right-coherence-triangle-identifications left right top p =
    map-equiv
      ( equiv-concat-right-coherence-triangle-identifications left right top p)

  equiv-concat-left-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {left' : a ＝ c} (p : left ＝ left') →
    coherence-triangle-identifications left' right top ≃
    coherence-triangle-identifications left right top
  equiv-concat-left-coherence-triangle-identifications left right top p =
    equiv-concat p (top ∙ right)

  concat-left-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b)
    {left' : a ＝ c} (p : left ＝ left') →
    coherence-triangle-identifications left' right top →
    coherence-triangle-identifications left right top
  concat-left-coherence-triangle-identifications left right top p =
    map-equiv
      ( equiv-concat-left-coherence-triangle-identifications left right top p)
```

### Horizontal pasting of commuting triangles of identifications

Consider a commuting diagram of identifications of the form

```text
  top-left   top-right
    a ---> b ---> c
      \    |    /
  left \   |m  / right
        \  |  /
         ∨ ∨ ∨
           d
```

Then the outer triangle commutes too. Indeed, an identification
`left ＝ top-left ∙ middle` is given. Then, an identification

```text
  top-left ∙ middle ＝ (top-left ∙ top-right) ∙ right
```

is obtained immediately by left whiskering the right triangle with the
identification `top-left`. Note that this direct construction of the coherence
of the outer commuting triangle of identifications avoids any use of
associativity.

```agda
module _
  {l : Level} {A : UU l}
  {a b c d : A} (left : a ＝ d) (middle : b ＝ d) (right : c ＝ d)
  (top-left : a ＝ b) (top-right : b ＝ c)
  where

  horizontal-pasting-coherence-triangle-identifications :
    coherence-triangle-identifications left middle top-left →
    coherence-triangle-identifications middle right top-right →
    coherence-triangle-identifications left right (top-left ∙ top-right)
  horizontal-pasting-coherence-triangle-identifications s t =
    ( s) ∙
    ( left-whisker-concat-coherence-triangle-identifications
      ( top-left)
      ( middle)
      ( right)
      ( top-right)
      ( t))
```

### Horizontal pasting of commuting triangles of identifications is a binary equivalence

```agda
module _
  {l : Level} {A : UU l}
  {a b c d : A} (left : a ＝ d) (middle : b ＝ d) (right : c ＝ d)
  (top-left : a ＝ b) (top-right : b ＝ c)
  where

  abstract
    is-equiv-horizontal-pasting-coherence-triangle-identifications :
      (s : coherence-triangle-identifications left middle top-left) →
      is-equiv
        ( horizontal-pasting-coherence-triangle-identifications
          ( left)
          ( middle)
          ( right)
          ( top-left)
          ( top-right)
          ( s))
    is-equiv-horizontal-pasting-coherence-triangle-identifications s =
      is-equiv-comp _ _
        ( is-equiv-left-whisker-concat-coherence-triangle-identifications
          ( top-left)
          ( middle)
          ( right)
          ( top-right))
        ( is-equiv-concat s _)

  equiv-horizontal-pasting-coherence-triangle-identifications :
    (s : coherence-triangle-identifications left middle top-left) →
    coherence-triangle-identifications middle right top-right ≃
    coherence-triangle-identifications left right (top-left ∙ top-right)
  pr1 (equiv-horizontal-pasting-coherence-triangle-identifications s) =
    horizontal-pasting-coherence-triangle-identifications _ _ _ _ _ s
  pr2 (equiv-horizontal-pasting-coherence-triangle-identifications s) =
    is-equiv-horizontal-pasting-coherence-triangle-identifications s

  abstract
    is-equiv-horizontal-pasting-coherence-triangle-identifications' :
      (t : coherence-triangle-identifications middle right top-right) →
      is-equiv
        ( λ s →
          horizontal-pasting-coherence-triangle-identifications
            ( left)
            ( middle)
            ( right)
            ( top-left)
            ( top-right)
            ( s)
            ( t))
    is-equiv-horizontal-pasting-coherence-triangle-identifications' t =
      is-equiv-concat' _
        ( left-whisker-concat-coherence-triangle-identifications
          ( top-left)
          ( middle)
          ( right)
          ( top-right)
          ( t))

  equiv-horizontal-pasting-coherence-triangle-identifications' :
    (t : coherence-triangle-identifications middle right top-right) →
    coherence-triangle-identifications left middle top-left ≃
    coherence-triangle-identifications left right (top-left ∙ top-right)
  pr1 (equiv-horizontal-pasting-coherence-triangle-identifications' t) s =
    horizontal-pasting-coherence-triangle-identifications
      ( left)
      ( middle)
      ( right)
      ( top-left)
      ( top-right)
      ( s)
      ( t)
  pr2 (equiv-horizontal-pasting-coherence-triangle-identifications' t) =
    is-equiv-horizontal-pasting-coherence-triangle-identifications' t

  is-binary-equiv-horizontal-pasting-coherence-triangle-identifications :
    is-binary-equiv
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( middle)
        ( right)
        ( top-left)
        ( top-right))
  pr1 is-binary-equiv-horizontal-pasting-coherence-triangle-identifications =
    is-equiv-horizontal-pasting-coherence-triangle-identifications'
  pr2 is-binary-equiv-horizontal-pasting-coherence-triangle-identifications =
    is-equiv-horizontal-pasting-coherence-triangle-identifications
```

### The left unit law for horizontal pastinf of commuting triangles of identifications

Consider a commuting triangle of identifications

```text
         top
     a ------> b
      \       /
  left \     / right
        \   /
         ∨ ∨
          c
```

with `t : left ＝ top ∙ right`. Then we have an identification

```text
  horizontal-pasting left left right refl top refl t ＝ t
```

```agda
module _
  {l : Level} {A : UU l} {a b c : A}
  where

  left-unit-law-horizontal-pasting-coherence-triangle-identifications :
    (left : a ＝ c) (right : b ＝ c) (top : a ＝ b) →
    (t : coherence-triangle-identifications left right top) →
    horizontal-pasting-coherence-triangle-identifications
      ( left)
      ( left)
      ( right)
      ( refl)
      ( top)
      ( refl)
      ( t) ＝
    t
  left-unit-law-horizontal-pasting-coherence-triangle-identifications
    ._ right top refl =
    refl
```

### The left unit law for horizontal pastinf of commuting triangles of identifications

Consider a commuting triangle of identifications

```text
         top
     a ------> b
      \       /
  left \     / right
        \   /
         ∨ ∨
          c
```

with `t : left ＝ top ∙ right`. Then we have a commuting triangle of
identifications

```text
      horizontal-pasting t refl
  left ----------------------> (top ∙ refl) ∙ right
       \                     /
        \                   /
       t \                 / right-whisker right-unit right
          \               /
           \             /
            ∨           ∨
             top ∙ right
```

```agda
module _
  {l : Level} {A : UU l} {a b c : A}
  where

  right-unit-law-horizontal-pasting-coherence-triangle-identifications :
    (left : a ＝ c) (right : b ＝ c) (top : a ＝ b) →
    (t : coherence-triangle-identifications left right top) →
    coherence-triangle-identifications
      ( t)
      ( right-whisker-concat right-unit right)
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( right)
        ( right)
        ( top)
        ( refl)
        ( t)
        ( refl))
  right-unit-law-horizontal-pasting-coherence-triangle-identifications
    ._ right refl refl = refl
```

### Associativity of horizontal pasting of coherences of commuting triangles of identifications

```agda
module _
  {l : Level} {A : UU l} {a b c d e : A}
  where

  associative-horizontal-pasting-coherence-triangle-identifications :
    (left : a ＝ e) (mid-left : b ＝ e) (mid-right : c ＝ e) (right : d ＝ e)
    (top-left : a ＝ b) (top-middle : b ＝ c) (top-right : c ＝ d)
    (r : coherence-triangle-identifications left mid-left top-left) →
    (s : coherence-triangle-identifications mid-left mid-right top-middle) →
    (t : coherence-triangle-identifications mid-right right top-right) →
    coherence-triangle-identifications
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( mid-left)
        ( right)
        ( top-left)
        ( top-middle ∙ top-right)
        ( r)
        ( horizontal-pasting-coherence-triangle-identifications
          ( mid-left)
          ( mid-right)
          ( right)
          ( top-middle)
          ( top-right)
          ( s)
          ( t)))
      ( right-whisker-concat (assoc top-left top-middle top-right) right)
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( mid-right)
        ( right)
        ( top-left ∙ top-middle)
        ( top-right)
        ( horizontal-pasting-coherence-triangle-identifications
          ( left)
          ( mid-left)
          ( mid-right)
          ( top-left)
          ( top-middle)
          ( r)
          ( s))
        ( t))
  associative-horizontal-pasting-coherence-triangle-identifications
    refl .refl .refl .refl refl refl refl refl refl refl =
    refl
```

### Left whiskering of horizontal pasting of commuting triangles of identifications

Consider two commuting triangles of identifications as in the diagram

```text
      s       t
  a ----> b ----> c
    \     |     /
     \  L |  R /
    l \   |m  / r
       \  |  /
        ∨ ∨ ∨
          d,
```

and consider furthermore a commuting triangle of identifications

```text
             t'
         b ----> c
         |     /
         | R' /
       m |   / r
         |  /
         ∨ ∨
         d
```

where the identifications `m : b ＝ d` and `r : c ＝ d` are the same as in the
previous diagram. Finally, consider an identification `p : t ＝ t'` and an
identification `q` witnessing that the triangle

```text
        R
   m ------> t ∙ r
    \       /
  R' \     / right-whisker p r
      \   /
       ∨ ∨
     t' ∙ r
```

commutes. Then the triangle

```text
                      horizontal-pasting L R
                      l ----------------> (s ∙ t) ∙ r
                        \               /
                         \             /
  horizontal-pasting L R' \           / right-whisker (left-whisker s p) r
                           \         /
                            ∨       ∨
                          (s ∙ t') ∙ r
```

commutes.

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  left-whisker-horizontal-pasting-coherence-triangle-identifications :
    (left : a ＝ d) (middle : b ＝ d) (right : c ＝ d)
    (top-left : a ＝ b) (top-right top-right' : b ＝ c) →
    (L : coherence-triangle-identifications left middle top-left)
    (R : coherence-triangle-identifications middle right top-right)
    (R' : coherence-triangle-identifications middle right top-right')
    (p : top-right ＝ top-right') →
    coherence-triangle-identifications R' (right-whisker-concat p right) R →
    coherence-triangle-identifications
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( middle)
        ( right)
        ( top-left)
        ( top-right')
        ( L)
        ( R'))
      ( right-whisker-concat (left-whisker-concat top-left p) right)
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( middle)
        ( right)
        ( top-left)
        ( top-right)
        ( L)
        ( R))
  left-whisker-horizontal-pasting-coherence-triangle-identifications
    ._ ._ refl refl refl .refl refl refl ._ refl refl =
    refl
```

### Right whiskering of horizontal pasting of commuting triangles of identifications

Consider two commuting triangles of identifications as in the diagram

```text
     s      t
  a ----> b ----> c
    \     |     /
     \  L |  R /
    l \   |m  / r
       \  |  /
        ∨ ∨ ∨
          d,
```

and consider furthermore a commuting triangle of identifications

```text
      s'
  a ----> b
    \     |
     \ L' |
    l \   |m
       \  |
        ∨ ∨
          d,
```

where the identifications `m : b ＝ d` and `l : a ＝ d` are the same as in the
previous diagram. Finally, consider an identification `p : s ＝ s'` and an
identification `q` witnessing that the triangle

```text
        L
   l ------> s ∙ m
    \       /
  L' \     / right-whisker p m
      \   /
       ∨ ∨
     s' ∙ r
```

commutes. Then the triangle

```text
                      horizontal-pasting L R
                      l ----------------> (s ∙ t) ∙ r
                        \               /
                         \             /
  horizontal-pasting L R' \           / right-whisker (right-whisker p t) r
                           \         /
                            ∨       ∨
                          (s' ∙ t) ∙ r
```

commutes.

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  where

  right-whisker-horizontal-pasting-coherence-triangle-identifications :
    (left : a ＝ d) (middle : b ＝ d) (right : c ＝ d)
    (top-left top-left' : a ＝ b) (top-right : b ＝ c) →
    (L : coherence-triangle-identifications left middle top-left)
    (L' : coherence-triangle-identifications left middle top-left')
    (R : coherence-triangle-identifications middle right top-right)
    (p : top-left ＝ top-left') →
    coherence-triangle-identifications L' (right-whisker-concat p middle) L →
    coherence-triangle-identifications
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( middle)
        ( right)
        ( top-left')
        ( top-right)
        ( L')
        ( R))
      ( right-whisker-concat (right-whisker-concat p top-right) right)
      ( horizontal-pasting-coherence-triangle-identifications
        ( left)
        ( middle)
        ( right)
        ( top-left)
        ( top-right)
        ( L)
        ( R))
  right-whisker-horizontal-pasting-coherence-triangle-identifications
    refl .refl .refl refl .refl refl refl ._ refl refl refl =
    refl
```

### Right pasting of commuting triangles of identifications

Consider a commuting diagram of identifications of the form

```text
          top
   a ------------> b
    \ ⎻⎽          /
     \  ⎺⎽ mid   / top-right
      \   ⎺⎽    ∨
  left \    ⎺> c
        \     /
         \   / bottom-right
          ∨ ∨
           d
```

Then the outer triangle commutes too. Indeed, an identification
`left ＝ mid ∙ bottom-right` is given. Then, an identification

```text
  mid ∙ bottom-right ＝ top ∙ (top-right ∙ bottom-right)
```

is obtained immediately by right whiskering the upper triangle with the
identification `bottom-right`. Note that this direct construction of the
coherence of the outer commuting triangle of identifications avoids any use of
associativity.

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  (left : a ＝ d) (top-right : b ＝ c) (bottom-right : c ＝ d)
  (middle : a ＝ c) (top : a ＝ b)
  where

  right-pasting-coherence-triangle-identifications :
    (s : coherence-triangle-identifications left bottom-right middle) →
    (t : coherence-triangle-identifications middle top-right top) →
    coherence-triangle-identifications left (top-right ∙ bottom-right) top
  right-pasting-coherence-triangle-identifications s t =
    ( s) ∙
    ( right-whisker-concat-coherence-triangle-identifications
      ( middle)
      ( top-right)
      ( top)
      ( bottom-right)
      ( t))
```

### Right pasting commuting triangles of identifications is a binary equivalence

```agda
module _
  {l : Level} {A : UU l} {a b c d : A}
  (left : a ＝ d) (top-right : b ＝ c) (bottom-right : c ＝ d)
  (middle : a ＝ c) (top : a ＝ b)
  where

  abstract
    is-equiv-right-pasting-coherence-triangle-identifications :
      (s : coherence-triangle-identifications left bottom-right middle) →
      is-equiv
        ( right-pasting-coherence-triangle-identifications
          ( left)
          ( top-right)
          ( bottom-right)
          ( middle)
          ( top)
          ( s))
    is-equiv-right-pasting-coherence-triangle-identifications s =
      is-equiv-comp _ _
        ( is-equiv-right-whisker-concat-coherence-triangle-identifications
          ( middle)
          ( top-right)
          ( top)
          ( bottom-right))
        ( is-equiv-concat s _)

  equiv-right-pasting-coherence-triangle-identifications :
    (s : coherence-triangle-identifications left bottom-right middle) →
    coherence-triangle-identifications middle top-right top ≃
    coherence-triangle-identifications left (top-right ∙ bottom-right) top
  pr1 (equiv-right-pasting-coherence-triangle-identifications s) =
    right-pasting-coherence-triangle-identifications
      ( left)
      ( top-right)
      ( bottom-right)
      ( middle)
      ( top)
      ( s)
  pr2 (equiv-right-pasting-coherence-triangle-identifications s) =
    is-equiv-right-pasting-coherence-triangle-identifications s

  abstract
    is-equiv-right-pasting-coherence-triangle-identifications' :
      (t : coherence-triangle-identifications middle top-right top) →
      is-equiv
        ( λ (s : coherence-triangle-identifications left bottom-right middle) →
          right-pasting-coherence-triangle-identifications
            ( left)
            ( top-right)
            ( bottom-right)
            ( middle)
            ( top)
            ( s)
            ( t))
    is-equiv-right-pasting-coherence-triangle-identifications' t =
      is-equiv-concat' _
        ( right-whisker-concat-coherence-triangle-identifications
          ( middle)
          ( top-right)
          ( top)
          ( bottom-right)
          ( t))

  equiv-right-pasting-coherence-triangle-identifications' :
    (t : coherence-triangle-identifications middle top-right top) →
    coherence-triangle-identifications left bottom-right middle ≃
    coherence-triangle-identifications left (top-right ∙ bottom-right) top
  pr1 (equiv-right-pasting-coherence-triangle-identifications' t) s =
    right-pasting-coherence-triangle-identifications
      ( left)
      ( top-right)
      ( bottom-right)
      ( middle)
      ( top)
      ( s)
      ( t)
  pr2 (equiv-right-pasting-coherence-triangle-identifications' t) =
    is-equiv-right-pasting-coherence-triangle-identifications' t

  is-binary-equiv-right-pasting-coherence-triangle-identifications :
    is-binary-equiv
      ( right-pasting-coherence-triangle-identifications
        ( left)
        ( top-right)
        ( bottom-right)
        ( middle)
        ( top))
  pr1 is-binary-equiv-right-pasting-coherence-triangle-identifications =
    is-equiv-right-pasting-coherence-triangle-identifications'
  pr2 is-binary-equiv-right-pasting-coherence-triangle-identifications =
    is-equiv-right-pasting-coherence-triangle-identifications
```

### Left pasting of commuting triangles of identifications

**Note.** For left pasting there are two potential constructions. One takes a
commuting diagram of identifications of the form

```text
                top
         a ------------> b
          \          ⎽⎻ /
  top-left \     m ⎽⎺  /
            ∨    ⎽⎺   /
             c <⎺    / right
              \     /
   bottom-left \   /
                ∨ ∨
                 d
```

and returns an identification witnessing that the outer triangle commutes. In
this case the top triangle is an ordinary commuting triangle of identifications,
and the bottom triangle is inverted along the top edge `m`.

The other left pasting of commuting triangles of identifications takes a
commuting diagram of identifications of the form

```text
                top
         a ------------> b
          \         ⎽-> /
  top-left \    m ⎽⎺   /
            ∨   ⎽⎺    /
             c ⎺     / right
              \     /
   bottom-left \   /
                ∨ ∨
                 d
```

and returns an identification witnessing that the outer rectangle commutes. In
this case the bottom triangle of identifications is an ordinary commuting
triangle of identifications, and the top triangle is inverted along the right
edge `m`.

Both constructions have yet to be formalized.

### Vertically pasting commuting squares and commuting triangles of identifications

Consider a diagram of the form

```text
                top
         a ------------> b
          \             /
  top-left \           / top-right
            ∨   mid   ∨
             c ----> d
              \     /
   bottom-left \   / bottom-right
                ∨ ∨
                 e
```

with `s : top-left ∙ mid ＝ top ∙ top-right` witnessing that the square
commutes, and with `t : bottom-left ＝ mid ∙ bottom-right` witnessing that the
triangle commutes. Then the outer triangle commutes.

```agda
module _
  {l : Level} {A : UU l}
  where

  vertical-pasting-coherence-square-coherence-triangle-identifications :
    {a b c d e : A}
    (top : a ＝ b) (top-left : a ＝ c) (top-right : b ＝ d) (mid : c ＝ d)
    (bottom-left : c ＝ e) (bottom-right : d ＝ e) →
    coherence-square-identifications top top-left top-right mid →
    coherence-triangle-identifications bottom-left bottom-right mid →
    coherence-triangle-identifications
      ( top-left ∙ bottom-left)
      ( top-right ∙ bottom-right)
      ( top)
  vertical-pasting-coherence-square-coherence-triangle-identifications
    top top-left top-right mid bottom-left bottom-right s t =
    ( left-whisker-concat top-left t) ∙
    ( right-whisker-concat-coherence-square-identifications
      ( top)
      ( top-left)
      ( top-right)
      ( mid)
      ( s)
      ( bottom-right))
```

### Vertical pasting of horizontally constant commuting squares of identifications and commuting triangles of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  vertical-pasting-coherence-horizontally-constant-square-coherence-triangle-identifications :
    {a c e : A} (p : a ＝ c)
    (bottom-left : c ＝ e) (bottom-right : c ＝ e) →
    (t : coherence-triangle-identifications bottom-left bottom-right refl) →
    ( vertical-pasting-coherence-square-coherence-triangle-identifications
      ( refl)
      ( p)
      ( p)
      ( refl)
      ( bottom-left)
      ( bottom-right)
      ( horizontal-refl-coherence-square-identifications p)
      ( t)) ＝
    ( left-whisker-concat p t)
  vertical-pasting-coherence-horizontally-constant-square-coherence-triangle-identifications
    refl refl .refl refl =
    refl
```

### Vertical pasting of vertically constant commuting squares of identifications and commuting triangles of identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  vertical-pasting-coherence-vertically-constant-square-coherence-triangle-identifications :
    {a b c : A} (left : a ＝ c) (right : b ＝ c) (top : a ＝ b) →
    (t : coherence-triangle-identifications left right top) →
    ( vertical-pasting-coherence-square-coherence-triangle-identifications
      ( top)
      ( refl)
      ( refl)
      ( top)
      ( left)
      ( right)
      ( vertical-refl-coherence-square-identifications top)
      ( t)) ＝
    t
  vertical-pasting-coherence-vertically-constant-square-coherence-triangle-identifications
    ._ refl refl refl = refl
```
