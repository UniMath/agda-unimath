# Commuting squares of homotopies

```agda
module foundation-core.commuting-squares-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-identifications
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies-concatenation
```

</details>

## Idea

A square of [homotopies](foundation-core.homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      ∨         ∨
      h ------> i
        bottom
```

is said to be a {{#concept "commuting square" Disambiguation="homotopies"}} of
homotopies if there is a homotopy `left ∙h bottom ~ top ∙h right `. Such a
homotopy is called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-homotopies}}
of the square.

## Definitions

### Commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  coherence-square-homotopies : UU (l1 ⊔ l2)
  coherence-square-homotopies =
    left ∙h bottom ~ top ∙h right

  coherence-square-homotopies' : UU (l1 ⊔ l2)
  coherence-square-homotopies' =
    top ∙h right ~ left ∙h bottom
```

### Horizontally constant squares

{{#concept "Horizontally constant squares" Disambiguation="homotopies" Agda=horizontal-refl-coherence-square-homotopies}}
are commuting squares of homotopies of the form

```text
       refl-htpy
    f ----------> f
    |             |
  H |             | H
    ∨             ∨
    g ----------> g.
       refl-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} (H : f ~ g)
  where

  horizontal-refl-coherence-square-homotopies :
    coherence-square-homotopies refl-htpy H H refl-htpy
  horizontal-refl-coherence-square-homotopies x =
    horizontal-refl-coherence-square-identifications (H x)
```

### Vertically constant squares

{{#concept "Vertically constant squares" Disambiguation="homotopies" Agda=vertical-refl-coherence-square-homotopies}}
are commuting squares of homotopies of the form

```text
                H
            f -----> g
            |        |
  refl-htpy |        | refl-htpy
            ∨        ∨
            f -----> g.
                H
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} (H : f ~ g)
  where

  vertical-refl-coherence-square-homotopies :
    coherence-square-homotopies H refl-htpy refl-htpy H
  vertical-refl-coherence-square-homotopies x =
    vertical-refl-coherence-square-identifications (H x)
```

### Squares with refl on the top and bottom

Given a homotopy `H ~ H'`, we can obtain a coherence square with `refl-htpy` on
the top and bottom.

```text
       refl-htpy
    f ----------> f
    |             |
  H |             | H'
    ∨             ∨
    g ----------> g
       refl-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  (H H' : f ~ g)
  where

  coherence-square-homotopies-horizontal-refl :
    H ~ H' →
    coherence-square-homotopies
      ( refl-htpy)
      ( H)
      ( H')
      ( refl-htpy)
  coherence-square-homotopies-horizontal-refl K =
    right-unit-htpy ∙h K
```

Conversely, given a coherence square as above, we can obtain a homotopy
`H ~ H'`.

```agda
  inv-coherence-square-homotopies-horizontal-refl :
    coherence-square-homotopies
      ( refl-htpy)
      ( H)
      ( H')
      ( refl-htpy) →
    H ~ H'
  inv-coherence-square-homotopies-horizontal-refl K =
    inv-htpy-right-unit-htpy ∙h K
```

### Squares with `refl-htpy` on the left and right

Given a homotopy `H ~ H'`, we can obtain a coherence square with `refl-htpy` on
the left and right.

```text
                 H'
            f ------> g
            |         |
  refl-htpy |         | refl-htpy
            ∨         ∨
            f ------> g
                 H
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  (H H' : f ~ g)
  where

  coherence-square-homotopies-vertical-refl :
    H ~ H' →
    coherence-square-homotopies
      ( H')
      ( refl-htpy)
      ( refl-htpy)
      ( H)
  coherence-square-homotopies-vertical-refl K =
    K ∙h inv-htpy right-unit-htpy
```

Conversely, given a coherence square as above, we can obtain a homotopy
`H ~ H'`.

```agda
  inv-coherence-square-homotopies-vertical-refl :
    coherence-square-homotopies
      ( H')
      ( refl-htpy)
      ( refl-htpy)
      ( H) →
    H ~ H'
  inv-coherence-square-homotopies-vertical-refl K =
    K ∙h right-unit-htpy
```

## Operations

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
              top⁻¹
        g ------------> f
        |               |
  right |               | left
        ∨               ∨
        i ------------> h
             bottom⁻¹
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
  horizontal-inv-coherence-square-homotopies top left right bottom H x =
    horizontal-inv-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
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
  left⁻¹ |          | right⁻¹
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
    vertical-inv-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

### Functions acting on squares of homotopies

Given a commuting square of homotopies

```text
           top
       f -------> g
       |          |
  left |          | right
       ∨          ∨
       h -------> i
          bottom
```

in `(x : A) → B x`, and given a dependent map `F : {x : A} → B x → C x`, the
square of homotopies

```text
                 F ·l top
           f f -----------> f g
            |                |
  F ·l left |                | F ·l right
            ∨                ∨
            h -------------> i
               F ·l bottom
```

commutes.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g h i : (x : A) → B x}
  (F : {x : A} → B x → C x)
  where

  map-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies
      ( F ·l top)
      ( F ·l left)
      ( F ·l right)
      ( F ·l bottom)
  map-coherence-square-homotopies top left right bottom H x =
    map-coherence-square-identifications
      ( F)
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

Similarly we may whisker it on the right.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  {f g h i : (y : B) → C y}
  where

  right-whisker-comp-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    (F : A → B) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies
      ( top ·r F)
      ( left ·r F)
      ( right ·r F)
      ( bottom ·r F)
  right-whisker-comp-coherence-square-homotopies top left right bottom F α =
    α ·r F
```

### Concatenating homotopies of edges and coherences of commuting squares of homotopies

Consider a commuting square of homotopies and a homotopy of one of the four
sides with another homotopy, as for example in the diagram below:

```text
             top
       a ---------> b
       |           | |
  left |     right |~| right'
       ∨           ∨ ∨
       c ---------> d.
           bottom
```

Then any homotopy witnessing that the square commutes can be concatenated with
the homotopy on the side, to obtain a new commuting square of homotopies.

**Note.** To avoid cyclic module dependencies we will give direct proofs that
concatenating homotopies of edges of a square with the coherence of its
commutativity is an equivalence.

#### Concatenating homotopies of the top edge with a coherence of a commuting square of homotopies

Consider a commuting diagram of homotopies

```text
           top'
         ------->
       f -------> g
       |   top    |
  left |          | right
       ∨          ∨
       h -------> i.
          bottom
```

with a homotopy `top ~ top'`. Then we get maps back and forth

```text
           top                             top'
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ↔    left |          | right
       ∨          ∨                    ∨          ∨
       h -------> i                    h -------> i.
          bottom                          bottom
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {top' : f ~ g} (s : top ~ top')
  where

  concat-top-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies top' left right bottom
  concat-top-homotopy-coherence-square-homotopies H x =
    concat-top-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)

  inv-concat-top-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top' left right bottom →
    coherence-square-homotopies top left right bottom
  inv-concat-top-homotopy-coherence-square-homotopies H x =
    inv-concat-top-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)
```

#### Concatenating homotopies of the left edge with a coherence of a commuting square of homotopies

Consider a commuting diagram of homotopies

```text
              top
         f -------> g
        | |         |
  left' | | left    | right
        ∨ ∨         ∨
         h -------> i.
            bottom
```

with a homotopy `left ~ left'`. Then we get maps back and forth

```text
           top                              top
       f -------> g                     f -------> g
       |          |                     |          |
  left |          | right    ↔    left' |          | right
       ∨          ∨                     ∨          ∨
       h -------> i                     h -------> i.
          bottom                           bottom
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {left' : f ~ h} (s : left ~ left')
  where

  concat-left-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies top left' right bottom
  concat-left-homotopy-coherence-square-homotopies H x =
    concat-left-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)

  inv-concat-left-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left' right bottom →
    coherence-square-homotopies top left right bottom
  inv-concat-left-homotopy-coherence-square-homotopies H x =
    inv-concat-left-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)
```

#### Concatenating homotopies of the right edge with a coherence of a commuting square of homotopies

Consider a commuting diagram of homotopies

```text
            top
       f -------> g
       |         | |
  left |   right | | right'
       ∨         ∨ ∨
       h -------> i.
          bottom
```

with a homotopy `right ~ right'`. Then we get maps back and forth

```text
           top                             top
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ↔    left |          | right'
       ∨          ∨                    ∨          ∨
       h -------> i                    h -------> i.
          bottom                          bottom
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {right' : g ~ i} (s : right ~ right')
  where

  concat-right-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies top left right' bottom
  concat-right-homotopy-coherence-square-homotopies H x =
    concat-right-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)

  inv-concat-right-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right' bottom →
    coherence-square-homotopies top left right bottom
  inv-concat-right-homotopy-coherence-square-homotopies H x =
    inv-concat-right-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).

#### Concatenating homotopies of the bottom edge with a coherence of a commuting square of homotopies

Consider a commuting diagram of homotopies

```text
            top
       f -------> g
       |          |
  left |          | right
       ∨  bottom  ∨
       h -------> i.
         ------->
          bottom'
```

with a homotopy `bottom ~ bottom'`. Then we get maps back and forth

```text
           top                             top
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ↔    left |          | right
       ∨          ∨                    ∨          ∨
       h -------> i                    h -------> i.
          bottom                          bottom'
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {bottom' : h ~ i} (s : bottom ~ bottom')
  where

  concat-bottom-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies top left right bottom'
  concat-bottom-homotopy-coherence-square-homotopies H x =
    concat-bottom-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)

  inv-concat-bottom-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom' →
    coherence-square-homotopies top left right bottom
  inv-concat-bottom-homotopy-coherence-square-homotopies H x =
    inv-concat-bottom-identification-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( s x)
      ( H x)
```

We record that this construction is an equivalence in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).

### Whiskering and splicing coherences of commuting squares of homotopies with respect to concatenation of homotopies

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

we may consider four ways of attaching new homotopies to it:

1. Prepending `H : u ~ f` to the left gives us a commuting square

   ```text
                H ∙h top
              u -------> g
              |          |
    H ∙h left |          | right
              ∨          ∨
              h -------> i.
                 bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((H ∙h left) ∙h bottom ~ (H ∙h top) ∙h right).
   ```

2. Appending a homotopy `H : i ~ u` to the right gives a commuting square of
   homotopies

   ```text
                   top
           f ------------> g
           |               |
      left |               | right ∙h H
           ∨               ∨
           h ------------> u.
              bottom ∙h H
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h (bottom ∙h H) ~ top ∙h (right ∙h H)).
   ```

3. Splicing a homotopy `H : h ~ u` and its inverse into the middle gives a
   commuting square of homotopies

   ```text
                      top
              f --------------> g
              |                 |
    left ∙h H |                 | right
              ∨                 ∨
              u --------------> i.
                 H⁻¹ ∙h bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((left ∙h H) ∙h (H⁻¹ ∙h bottom) ~ top ∙h right).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((left ∙h H⁻¹) ∙h (H ∙h bottom) ~ top ∙h right).
   ```

4. Splicing a homotopy `H : g ~ u` and its inverse into the middle gives a
   commuting square of homotopies

   ```text
            top ∙h H
          f --------> u
          |           |
     left |           | H⁻¹ ∙h right
          ∨           ∨
          h --------> i.
             bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h bottom ~ (top ∙h H) ∙h (H⁻¹ ∙h right)).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h bottom ~ (top ∙h H⁻¹) ∙h (H ∙h right)).
   ```

These operations are useful in proofs involving homotopy algebra, because taking
`equiv-right-whisker-concat-coherence-square-homotopies` as an example, it
provides us with two maps: the forward direction states
`(H ∙h r ~ K ∙h s) → (H ∙h (r ∙h t)) ~ K ∙h (s ∙h t))`, which allows one to
append a homotopy without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out a homotopy in parentheses.

#### Left whiskering coherences of commuting squares of homotopies

For any homotopy `H : u ~ f` we obtain maps back and forth

```text
           top                                H ∙h top
       f -------> g                         u -------> g
       |          |                         |          |
  left |          | right    ↔    H ∙h left |          | right
       ∨          ∨                         ∨          ∨
       h -------> i                         h -------> i
          bottom                               bottom
```

of coherences of commuting squares of homotopies. We show in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md)
that these maps are equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  left-whisker-concat-coherence-square-homotopies :
    {u : (x : A) → B x} (H : u ~ f)
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies (H ∙h top) (H ∙h left) right bottom
  left-whisker-concat-coherence-square-homotopies
    H top left right bottom coh x =
    left-whisker-concat-coherence-square-identifications
      ( H x)
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( coh x)

  left-unwhisker-concat-coherence-square-homotopies :
    {u : (x : A) → B x} (H : u ~ f)
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies (H ∙h top) (H ∙h left) right bottom →
    coherence-square-homotopies top left right bottom
  left-unwhisker-concat-coherence-square-homotopies
    H top left right bottom coh x =
    left-unwhisker-concat-coherence-square-identifications
      ( H x)
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( coh x)
```

#### Right whiskering coherences of commuting squares of homotopies

For any homotopy `H : i ~ u` we obtain maps back and forth

```text
           top                                 top
       f -------> g                     f ------------> g
       |          |                     |               |
  left |          | right    ↔     left |               | right ∙h H
       ∨          ∨                     ∨               ∨
       h -------> i                     h ------------> i
          bottom                           bottom ∙h H
```

of coherences of commuting squares of homotopies. We show in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md)
that these maps are equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  right-whisker-concat-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom →
    {u : (x : A) → B x} (H : i ~ u) →
    coherence-square-homotopies top left (right ∙h H) (bottom ∙h H)
  right-whisker-concat-coherence-square-homotopies coh H x =
    right-whisker-concat-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( coh x)
      ( H x)

  right-unwhisker-cohernece-square-homotopies :
    {u : (x : A) → B x} (H : i ~ u) →
    coherence-square-homotopies top left (right ∙h H) (bottom ∙h H) →
    coherence-square-homotopies top left right bottom
  right-unwhisker-cohernece-square-homotopies H coh x =
    right-unwhisker-cohernece-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
      ( coh x)
```

### Double whiskering of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h u v i : (x : A) → B x}
  where

  double-whisker-coherence-square-homotopies :
    (p : f ~ g)
    (top : g ~ u) (left : g ~ h) (right : u ~ v) (bottom : h ~ v)
    (s : v ~ i) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies
      ( p ∙h top)
      ( p ∙h left)
      ( right ∙h s)
      ( bottom ∙h s)
  double-whisker-coherence-square-homotopies p top left right bottom q H =
    left-whisker-concat-coherence-square-homotopies p top left
      ( right ∙h q)
      ( bottom ∙h q)
    ( right-whisker-concat-coherence-square-homotopies
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( H)
      ( q))
```

#### Left splicing coherences of commuting squares of homotopies

For any inverse pair of homotopies `H : g ~ u` and `K : u ~ g` equipped with
`α : inv-htpy H ~ K` we obtain maps back and forth

```text
           top                                    top
       f -------> g                         f -----------> g
       |          |                         |              |
  left |          | right    ↔    left ∙h H |              | right
       ∨          ∨                         ∨              ∨
       h -------> i                         u -----------> i
          bottom                               K ∙h bottom
```

of coherences of commuting squares of homotopies. We show in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md)
that these maps are equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  left-splice-coherence-square-homotopies :
    {u : (x : A) → B x} (H : h ~ u) (K : u ~ h) (α : inv-htpy H ~ K) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies top (left ∙h H) right (K ∙h bottom)
  left-splice-coherence-square-homotopies H K α coh x =
    left-splice-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
      ( K x)
      ( α x)
      ( coh x)

  left-unsplice-coherence-square-homotopies :
    {u : (x : A) → B x} (H : h ~ u) (K : u ~ h) (α : inv-htpy H ~ K) →
    coherence-square-homotopies top (left ∙h H) right (K ∙h bottom) →
    coherence-square-homotopies top left right bottom
  left-unsplice-coherence-square-homotopies H K α coh x =
    left-unsplice-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
      ( K x)
      ( α x)
      ( coh x)
```

#### Right splicing coherences of commuting squares of homotopies

For any inverse pair of homotopies `H : g ~ u` and `K : u ~ g` equipped with
`α : inv-htpy H ~ K` we obtain maps back and forth

```text
           top                             top ∙h H
       f -------> g                     f --------> u
       |          |                     |           |
  left |          | right    ↔     left |           | K ∙h right
       ∨          ∨                     ∨           ∨
       h -------> i                     h --------> i
          bottom                           bottom
```

of coherences of commuting squares of homotopies. We show in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md)
that these maps are equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  right-splice-coherence-square-homotopies :
    {u : (x : A) → B x} (H : g ~ u) (K : u ~ g) (α : inv-htpy H ~ K) →
    coherence-square-homotopies top left right bottom →
    coherence-square-homotopies (top ∙h H) left (inv-htpy H ∙h right) bottom
  right-splice-coherence-square-homotopies H K α coh x =
    right-splice-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
      ( K x)
      ( α x)
      ( coh x)

  right-unsplice-coherence-square-homotopies :
    {u : (x : A) → B x} (H : g ~ u) (K : u ~ g) (α : inv-htpy H ~ K) →
    coherence-square-homotopies (top ∙h H) left (inv-htpy H ∙h right) bottom →
    coherence-square-homotopies top left right bottom
  right-unsplice-coherence-square-homotopies H K α coh x =
    right-unsplice-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
      ( K x)
      ( α x)
      ( coh x)
```

### Horizontally pasting squares of homotopies

Consider two squares of homotopies as in the diagram

```text
            top-left         top-right
       a -------------> b -------------> c
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       d -------------> e -------------> f
          bottom-left      bottom-right
```

with `H : left ∙h bottom-left ~ top-left ∙h middle` and
`K : middle ∙h bottom-right ~ top-right ∙h right`. Then the outer square
commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a b c d e f : (x : A) → B x}
  (top-left : a ~ b) (top-right : b ~ c)
  (left : a ~ d) (middle : b ~ e) (right : c ~ f)
  (bottom-left : d ~ e) (bottom-right : e ~ f)
  where

  horizontal-pasting-coherence-square-homotopies :
    coherence-square-homotopies top-left left middle bottom-left →
    coherence-square-homotopies top-right middle right bottom-right →
    coherence-square-homotopies
      (top-left ∙h top-right) left right (bottom-left ∙h bottom-right)
  horizontal-pasting-coherence-square-homotopies H K x =
    horizontal-pasting-coherence-square-identifications
      ( top-left x)
      ( top-right x)
      ( left x)
      ( middle x)
      ( right x)
      ( bottom-left x)
      ( bottom-right x)
      ( H x)
      ( K x)
```

### Vertically pasting squares of homotopies

Consider two squares of homotopies as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

with `H : top-left ∙h middle ~ top ∙h top-right` and
`K : bottom-left ∙h bottom ~ middle ∙h bottom-right`. Then the outer square
commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a b c d e f : (x : A) → B x}
  (top : a ~ b) (top-left : a ~ c) (top-right : b ~ d)
  (middle : c ~ d) (bottom-left : c ~ e) (bottom-right : d ~ f)
  (bottom : e ~ f)
  where

  vertical-pasting-coherence-square-homotopies :
    coherence-square-homotopies top top-left top-right middle →
    coherence-square-homotopies middle bottom-left bottom-right bottom →
    coherence-square-homotopies
      top (top-left ∙h bottom-left) (top-right ∙h bottom-right) bottom
  vertical-pasting-coherence-square-homotopies H K x =
    vertical-pasting-coherence-square-identifications
      ( top x)
      ( top-left x)
      ( top-right x)
      ( middle x)
      ( bottom-left x)
      ( bottom-right x)
      ( bottom x)
      ( H x)
      ( K x)
```

## Properties

### Left unit law for horizontal pasting of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  left-unit-law-horizontal-pasting-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    (H : coherence-square-homotopies top left right bottom) →
    horizontal-pasting-coherence-square-homotopies
      ( refl-htpy)
      ( top)
      ( left)
      ( left)
      ( right)
      ( refl-htpy)
      ( bottom)
      ( horizontal-refl-coherence-square-homotopies left)
      ( H) ~
    H
  left-unit-law-horizontal-pasting-coherence-square-homotopies
    top left right bottom H x =
    left-unit-law-horizontal-pasting-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

### Right unit law for horizontal pasting of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  right-unit-law-horizontal-pasting-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    (H : coherence-square-homotopies top left right bottom) →
    horizontal-pasting-coherence-square-homotopies
      ( top)
      ( refl-htpy)
      ( left)
      ( right)
      ( right)
      ( bottom)
      ( refl-htpy)
      ( H)
      ( horizontal-refl-coherence-square-homotopies right) ∙h
    right-whisker-concat-htpy right-unit-htpy right ~
    left-whisker-concat-htpy left right-unit-htpy ∙h H
  right-unit-law-horizontal-pasting-coherence-square-homotopies
    top left right bottom H x =
    right-unit-law-horizontal-pasting-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

### Left unit law for vertical pasting of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  left-unit-law-vertical-pasting-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    (H : coherence-square-homotopies top left right bottom) →
    vertical-pasting-coherence-square-homotopies
      ( top)
      ( refl-htpy)
      ( refl-htpy)
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( vertical-refl-coherence-square-homotopies top)
      ( H) ~
    H
  left-unit-law-vertical-pasting-coherence-square-homotopies
    top left right bottom H x =
    left-unit-law-vertical-pasting-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

### Right unit law for vertical pasting of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  where

  right-unit-law-vertical-pasting-coherence-square-homotopies :
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    (H : coherence-square-homotopies top left right bottom) →
    vertical-pasting-coherence-square-homotopies
      ( top)
      ( left)
      ( right)
      ( bottom)
      ( refl-htpy)
      ( refl-htpy)
      ( bottom)
      ( H)
      ( vertical-refl-coherence-square-homotopies bottom) ∙h
    left-whisker-concat-htpy top right-unit-htpy ~
    right-whisker-concat-htpy right-unit-htpy bottom ∙h H
  right-unit-law-vertical-pasting-coherence-square-homotopies
    top left right bottom H x =
    right-unit-law-vertical-pasting-coherence-square-identifications
      ( top x)
      ( left x)
      ( right x)
      ( bottom x)
      ( H x)
```

### Computing the right whiskering of a vertically constant square with a homotopy

Consider the vertically constant square of homotopies

```text
           H
       f -----> g
       |        |
  refl |        | refl
       ∨        ∨
       f -----> g
           H
```

at a homotopy `H : f ~ g`, and consider a homotopy `K : g ~ h`. Then the right
whiskering of the above square with `K` is the commuting square of homotopies

```text
            H
       f -------> g
       |          |
  refl |   refl   | K
       ∨          ∨
       f -------> h
          H ∙h K
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  right-whisker-concat-vertical-refl-coherence-square-homotopies :
    (H : f ~ g) (K : g ~ h) →
    right-whisker-concat-coherence-square-homotopies H refl-htpy refl-htpy H
      ( vertical-refl-coherence-square-homotopies H)
      ( K) ~
    refl-htpy
  right-whisker-concat-vertical-refl-coherence-square-homotopies H K x =
    right-whisker-concat-vertical-refl-coherence-square-identifications
      ( H x)
      ( K x)
```

### Computing the right whiskering of a horizontally constant square with a homotopy

Consider a horizontally constant commuting square of homotopies

```text
       refl-htpy
    f ----------> f
    |             |
  H |             | H
    ∨             ∨
    g ----------> g
       refl-htpy
```

at a homotopy `H` and consider a homotopy `K : g ~ h`. Then the right whiskering
of the above square with `K` is the square

```text
       refl-htpy
    f ----------> f
    |             |
  H |  refl-htpy  | H ∙h K
    ∨             ∨
    g ----------> h.
           K
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  right-whisker-concat-horizontal-refl-coherence-square-homotopies :
    (H : f ~ g) (K : g ~ h) →
    right-whisker-concat-coherence-square-homotopies refl-htpy H H refl-htpy
      ( horizontal-refl-coherence-square-homotopies H)
      ( K) ~
    refl-htpy
  right-whisker-concat-horizontal-refl-coherence-square-homotopies H K x =
    right-whisker-concat-horizontal-refl-coherence-square-identifications
      ( H x)
      ( K x)
```

### Computing the left whiskering of a horizontally constant square with a homotopy

Consider a homotopy `H : f ~ g` and a horizontally constant commuting square of
homotopies

```text
       refl-htpy
    g ----------> g
    |             |
  K |             | K
    ∨             ∨
    h ----------> h
       refl-htpy
```

at a homotopy `K : g ~ h`. The the left whiskering of the above square with `H`
is the commuting square

```text
                                    K ∙h refl-htpy
         f -----------------------------------------------------------------> g
         |                                                                    |
  K ∙h H | right-unit-htpy ∙h (right-whisker-concat-htpy right-unit-htpy H)⁻¹ | H
         ∨                                                                    ∨
         h -----------------------------------------------------------------> h.
                                      refl-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  left-whisker-concat-horizontal-refl-coherence-square-homotopies :
    (H : f ~ g) (K : g ~ h) →
    left-whisker-concat-coherence-square-homotopies H refl-htpy K K refl-htpy
      ( horizontal-refl-coherence-square-homotopies K) ∙h
    right-whisker-concat-htpy right-unit-htpy K ~
    right-unit-htpy
  left-whisker-concat-horizontal-refl-coherence-square-homotopies H K x =
    left-whisker-concat-horizontal-refl-coherence-square-identifications
      ( H x)
      ( K x)

  left-whisker-concat-horizontal-refl-coherence-square-homotopies' :
    (H : f ~ g) (K : g ~ h) →
    left-whisker-concat-coherence-square-homotopies H refl-htpy K K refl-htpy
      ( horizontal-refl-coherence-square-homotopies K) ~
    right-unit-htpy ∙h inv-htpy (right-whisker-concat-htpy right-unit-htpy K)
  left-whisker-concat-horizontal-refl-coherence-square-homotopies' H K x =
    left-whisker-concat-horizontal-refl-coherence-square-identifications'
      ( H x)
      ( K x)
```

### Computing the left whiskering of a vertically constant square with a homotopy

Consider the vertically constant square of homotopies

```text
                K
            g -----> h
            |        |
  refl-htpy |        | refl-htpy
            ∨        ∨
            g -----> h
                K
```

at a homotopy `K : g ~ h` and consider a homotopy `H : f ~ g`. Then the left
whiskering of the above square with `H` is the square

```text
                                            H ∙h K
                 f ----------------------------------------------------------> h
                 |                                                             |
  H ∙h refl-htpy | right-whisker-concat-htpy right-unit-htpy K ∙h right-unit⁻¹ | refl-htpy
                 ∨                                                             ∨
                 g ----------------------------------------------------------> h.
                                              K
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  left-whisker-concat-vertical-refl-coherence-square-homotopies :
    (H : f ~ g) (K : g ~ h) →
    left-whisker-concat-coherence-square-homotopies H K refl-htpy refl-htpy K
      ( vertical-refl-coherence-square-homotopies K) ∙h
    right-unit-htpy ~
    right-whisker-concat-htpy right-unit-htpy K
  left-whisker-concat-vertical-refl-coherence-square-homotopies H K x =
    left-whisker-concat-vertical-refl-coherence-square-identifications
      ( H x)
      ( K x)

  left-whisker-concat-vertical-refl-coherence-square-homotopies' :
    (H : f ~ g) (K : g ~ h) →
    left-whisker-concat-coherence-square-homotopies H K refl-htpy refl-htpy K
      ( vertical-refl-coherence-square-homotopies K) ~
    right-whisker-concat-htpy right-unit-htpy K ∙h inv-htpy right-unit-htpy
  left-whisker-concat-vertical-refl-coherence-square-homotopies' H K x =
    left-whisker-concat-vertical-refl-coherence-square-identifications'
      ( H x)
      ( K x)
```

### Left whiskering horizontal concatenations of squares with homotopies

Consider a commuting diagram of homotopies of the form

```text
            top-left        top-right
       a -------------> c -------------> e
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       b -------------> d -------------> f
          bottom-left      bottom-right
```

and consider a homotopy `H : f ~ a`. Then the left whiskering of `H` and the
horizontal concatenation of coherences of commuting squares is up to
associativity the horizontal concatenation of the squares

```text
               H ∙h top-left      top-right
            u -------------> c -------------> e
            |                |                |
  H ∙h left |                | middle         | right
            ∨                ∨                ∨
            b -------------> d -------------> f
               bottom-left      bottom-right
```

where the left square is the left whiskering of `H` and the original left
square.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-whisker-concat-horizontal-pasting-coherence-square-homotopies :
    {u a b c d e f : (x : A) → B x} (H : u ~ a)
    (top-left : a ~ c) (top-right : c ~ e)
    (left : a ~ b) (middle : c ~ d) (right : e ~ f)
    (bottom-left : b ~ d) (bottom-right : d ~ f)
    (l : coherence-square-homotopies top-left left middle bottom-left)
    (r : coherence-square-homotopies top-right middle right bottom-right) →
    left-whisker-concat-coherence-square-homotopies H
      ( top-left ∙h top-right)
      ( left)
      ( right)
      ( bottom-left ∙h bottom-right)
      ( horizontal-pasting-coherence-square-homotopies
        ( top-left)
        ( top-right)
        ( left)
        ( middle)
        ( right)
        ( bottom-left)
        ( bottom-right)
        ( l)
        ( r)) ~
    horizontal-pasting-coherence-square-homotopies
      ( H ∙h top-left)
      ( top-right)
      ( H ∙h left)
      ( middle)
      ( right)
      ( bottom-left)
      ( bottom-right)
      ( left-whisker-concat-coherence-square-homotopies H
        ( top-left)
        ( left)
        ( middle)
        ( bottom-left)
        ( l))
      ( r) ∙h
    right-whisker-concat-htpy
      ( assoc-htpy H top-left top-right)
      ( right)
  left-whisker-concat-horizontal-pasting-coherence-square-homotopies
    H top-left top-right left middle right bottom-left bottom-right l r x =
    left-whisker-concat-horizontal-pasting-coherence-square-identifications
      ( H x)
      ( top-left x)
      ( top-right x)
      ( left x)
      ( middle x)
      ( right x)
      ( bottom-left x)
      ( bottom-right x)
      ( l x)
      ( r x)
```

### Left whiskering vertical concatenations of squares with homotopies

Consider two squares of homotopies as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

and consider a homotopy `H : f ~ a`. Then the left whiskering of `H` with the
vertical pasting of the two squares above is up to associativity the vertical
pasting of the squares

```text
                  H ∙h top
                u --------> b
                |           |
  H ∙h top-left |           | top-right
                ∨  middle   ∨
                c --------> d
                |           |
    bottom-left |           | bottom-right
                ∨           ∨
                e --------> f.
                   bottom
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  left-whisker-concat-vertical-concat-coherence-square-homotopies :
    {u a b c d e f : (x : A) → B x} (H : u ~ a) →
    (top : a ~ b) (top-left : a ~ c) (top-right : b ~ d) (middle : c ~ d)
    (bottom-left : c ~ e) (bottom-right : d ~ f) (bottom : e ~ f)
    (t : coherence-square-homotopies top top-left top-right middle) →
    (b :
      coherence-square-homotopies middle bottom-left bottom-right bottom) →
    right-whisker-concat-htpy (assoc-htpy H top-left bottom-left) bottom ∙h
    left-whisker-concat-coherence-square-homotopies H
      ( top)
      ( top-left ∙h bottom-left)
      ( top-right ∙h bottom-right)
      ( bottom)
      ( vertical-pasting-coherence-square-homotopies
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( t)
        ( b)) ~
    vertical-pasting-coherence-square-homotopies
      ( H ∙h top)
      ( H ∙h top-left)
      ( top-right)
      ( middle)
      ( bottom-left)
      ( bottom-right)
      ( bottom)
      ( left-whisker-concat-coherence-square-homotopies H
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( t))
      ( b)
  left-whisker-concat-vertical-concat-coherence-square-homotopies
    H top top-left top-right middle bottom-left bottom-right bottom t b x =
    left-whisker-concat-vertical-concat-coherence-square-identifications
      ( H x)
      ( top x)
      ( top-left x)
      ( top-right x)
      ( middle x)
      ( bottom-left x)
      ( bottom-right x)
      ( bottom x)
      ( t x)
      ( b x)
```

### Right whiskering horizontal pastings of commuting squares of homotopies

Consider a commuting diagram of homotopies of the form

```text
            top-left        top-right
       a -------------> c -------------> e
       |                |                |
  left |                | middle         | right
       ∨                ∨                ∨
       b -------------> d -------------> f
          bottom-left      bottom-right
```

and consider a homotopy `K : f ~ g`. Then the right whiskering of the horizontal
pasting of the squares above is up to associativity the horizontal pasting of
the squares

```text
            top-left           top-right
       a -------------> c ------------------> e
       |                |                     |
  left |                | middle              | right ∙h K
       ∨                ∨                     ∨
       b -------------> d ------------------> g
          bottom-left      bottom-right ∙h K
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-whisker-concat-horizontal-pasting-coherence-square-homotopies :
    {a b c d e f g : (x : A) → B x}
    (top-left : a ~ c) (top-right : c ~ e)
    (left : a ~ b) (middle : c ~ d) (right : e ~ f)
    (bottom-left : b ~ d) (bottom-right : d ~ f)
    (l : coherence-square-homotopies top-left left middle bottom-left) →
    (r : coherence-square-homotopies top-right middle right bottom-right) →
    (K : f ~ g) →
    right-whisker-concat-coherence-square-homotopies
      ( top-left ∙h top-right)
      ( left)
      ( right)
      ( bottom-left ∙h bottom-right)
      ( horizontal-pasting-coherence-square-homotopies
        ( top-left)
        ( top-right)
        ( left)
        ( middle)
        ( right)
        ( bottom-left)
        ( bottom-right)
        ( l)
        ( r))
      ( K) ~
    left-whisker-concat-htpy left (assoc-htpy bottom-left bottom-right K) ∙h
    horizontal-pasting-coherence-square-homotopies
      ( top-left)
      ( top-right)
      ( left)
      ( middle)
      ( right ∙h K)
      ( bottom-left)
      ( bottom-right ∙h K)
      ( l)
      ( right-whisker-concat-coherence-square-homotopies
        ( top-right)
        ( middle)
        ( right)
        ( bottom-right)
        ( r)
        ( K))
  right-whisker-concat-horizontal-pasting-coherence-square-homotopies
    top-left top-right left middle right bottom-left bottom-right l r K x =
    right-whisker-concat-horizontal-pasting-coherence-square-identifications
      ( top-left x)
      ( top-right x)
      ( left x)
      ( middle x)
      ( right x)
      ( bottom-left x)
      ( bottom-right x)
      ( l x)
      ( r x)
      ( K x)
```

### Right whiskering vertical concatenations of squares with homotopies

Consider two squares of homotopies as in the diagram

```text
                  top
              a --------> b
              |           |
     top-left |           | top-right
              ∨  middle   ∨
              c --------> d
              |           |
  bottom-left |           | bottom-right
              ∨           ∨
              e --------> f
                 bottom
```

and consider a homotopy `K : f ~ g`. Then the right whiskering of the vertical
pasting of the two squares above with `K` is up to associativity the vertical
pasting of the squares

```text
                     top
              a ------------> b
              |               |
     top-left |               | top-right
              ∨    middle     ∨
              c ------------> d
              |               |
  bottom-left |               | bottom-right ∙h K
              ∨               ∨
              e ------------> g.
                 bottom ∙h K
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  right-whisker-concat-vertical-pasting-coherence-square-homotopies :
    {a b c d e f g : (x : A) → B x}
    (top : a ~ b) (top-left : a ~ c) (top-right : b ~ d)
    (middle : c ~ d)
    (bottom-left : c ~ e) (bottom-right : d ~ f) (bottom : e ~ f)
    (t : coherence-square-homotopies top top-left top-right middle) →
    (b :
      coherence-square-homotopies middle bottom-left bottom-right bottom) →
    (K : f ~ g) →
    right-whisker-concat-coherence-square-homotopies
      ( top)
      ( top-left ∙h bottom-left)
      ( top-right ∙h bottom-right)
      ( bottom)
      ( vertical-pasting-coherence-square-homotopies
        ( top)
        ( top-left)
        ( top-right)
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( t)
        ( b))
      ( K) ∙h
    left-whisker-concat-htpy top (assoc-htpy top-right bottom-right K) ~
    vertical-pasting-coherence-square-homotopies
      ( top)
      ( top-left)
      ( top-right)
      ( middle)
      ( bottom-left)
      ( bottom-right ∙h K)
      ( bottom ∙h K)
      ( t)
      ( right-whisker-concat-coherence-square-homotopies
        ( middle)
        ( bottom-left)
        ( bottom-right)
        ( bottom)
        ( b)
        ( K))
  right-whisker-concat-vertical-pasting-coherence-square-homotopies
    top top-left top-right middle bottom-left bottom-right bottom t b K x =
    right-whisker-concat-vertical-pasting-coherence-square-identifications
      ( top x)
      ( top-left x)
      ( top-right x)
      ( middle x)
      ( bottom-left x)
      ( bottom-right x)
      ( bottom x)
      ( t x)
      ( b x)
      ( K x)
```
