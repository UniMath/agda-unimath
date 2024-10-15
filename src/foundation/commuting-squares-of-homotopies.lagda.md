# Commuting squares of homotopies

```agda
module foundation.commuting-squares-of-homotopies where

open import foundation-core.commuting-squares-of-homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-function-types
```

</details>

## Idea

A square of [homotopies](foundation-core.identity-types.md)

```text
           top
       f -------> g
       |          |
  left |          | right
       ∨          ∨
       h -------> i
          bottom
```

is said to be a
{{#concept "commuting square" Disambiguation="homotopies" Agda=coherence-square-homotopies}}
if there is a homotopy `left ∙h bottom ~ top ∙h right`. Such a homotopy is
called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-homotopies}}
of the square.

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

with a homotopy `top ~ top'`. Then we get an equivalence

```text
           top                             top'
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ≃    left |          | right
       ∨          ∨                    ∨          ∨
       h -------> i                    h -------> i.
          bottom                          bottom
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {top' : f ~ g} (s : top ~ top')
  where

  abstract
    is-equiv-concat-top-homotopy-coherence-square-homotopies :
      is-equiv
        ( concat-top-homotopy-coherence-square-homotopies
            top left right bottom s)
    is-equiv-concat-top-homotopy-coherence-square-homotopies =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ x →
          is-equiv-concat-top-identification-coherence-square-identifications
            ( top x) (left x) (right x) (bottom x) (s x))

  equiv-concat-top-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top' left right bottom
  pr1 equiv-concat-top-homotopy-coherence-square-homotopies =
    concat-top-homotopy-coherence-square-homotopies top left right bottom s
  pr2 equiv-concat-top-homotopy-coherence-square-homotopies =
    is-equiv-concat-top-homotopy-coherence-square-homotopies
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

with a homotopy `left ~ left'`. Then we get an equivalence

```text
           top                              top
       f -------> g                     f -------> g
       |          |                     |          |
  left |          | right    ≃    left' |          | right
       ∨          ∨                     ∨          ∨
       h -------> i                     h -------> i.
          bottom                           bottom
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  {left' : f ~ h} (s : left ~ left')
  where

  abstract
    is-equiv-concat-left-homotopy-coherence-square-homotopies :
      is-equiv
        ( concat-left-homotopy-coherence-square-homotopies
            top left right bottom s)
    is-equiv-concat-left-homotopy-coherence-square-homotopies =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ x →
          is-equiv-concat-left-identification-coherence-square-identifications
            ( top x) (left x) (right x) (bottom x) (s x))

  equiv-concat-left-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top left' right bottom
  pr1 equiv-concat-left-homotopy-coherence-square-homotopies =
    concat-left-homotopy-coherence-square-homotopies top left right bottom s
  pr2 equiv-concat-left-homotopy-coherence-square-homotopies =
    is-equiv-concat-left-homotopy-coherence-square-homotopies
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

with a homotopy `right ~ right'`. Then we get an equivalence

```text
           top                             top
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ≃    left |          | right'
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

  abstract
    is-equiv-concat-right-homotopy-coherence-square-homotopies :
      is-equiv
        ( concat-right-homotopy-coherence-square-homotopies
            top left right bottom s)
    is-equiv-concat-right-homotopy-coherence-square-homotopies =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ x →
          is-equiv-concat-right-identification-coherence-square-identifications
            ( top x) (left x) (right x) (bottom x) (s x))

  equiv-concat-right-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top left right' bottom
  pr1 equiv-concat-right-homotopy-coherence-square-homotopies =
    concat-right-homotopy-coherence-square-homotopies top left right bottom s
  pr2 equiv-concat-right-homotopy-coherence-square-homotopies =
    is-equiv-concat-right-homotopy-coherence-square-homotopies
```

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

with a homotopy `bottom ~ bottom'`. Then we get an equivalence

```text
           top                             top
       f -------> g                    f -------> g
       |          |                    |          |
  left |          | right    ≃    left |          | right
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

  is-equiv-concat-bottom-homotopy-coherence-square-homotopies :
    is-equiv
      ( concat-bottom-homotopy-coherence-square-homotopies
          top left right bottom s)
  is-equiv-concat-bottom-homotopy-coherence-square-homotopies =
      is-equiv-map-Π-is-fiberwise-equiv
        ( λ x →
          is-equiv-concat-bottom-identification-coherence-square-identifications
            ( top x) (left x) (right x) (bottom x) (s x))

  equiv-concat-bottom-homotopy-coherence-square-homotopies :
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top left right bottom'
  pr1 equiv-concat-bottom-homotopy-coherence-square-homotopies =
    concat-bottom-homotopy-coherence-square-homotopies top left right bottom s
  pr2 equiv-concat-bottom-homotopy-coherence-square-homotopies =
    is-equiv-concat-bottom-homotopy-coherence-square-homotopies
```

### Whiskering and splicing coherences of commuting squares of homotopies

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

1. Prepending `p : u ~ f` to the left gives us a commuting square

   ```text
                p ∙h top
              u -------> g
              |          |
     p ∙h left |          | right
              ∨          ∨
              h -------> i.
                 bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((p ∙h left) ∙h bottom ~ (p ∙h top) ∙h right).
   ```

2. Appending a homotopy `p : i ~ u` to the right gives a commuting square of
   homotopies

   ```text
                   top
           f ------------> g
           |               |
      left |               | right ∙h p
           ∨               ∨
           h ------------> u.
              bottom ∙h p
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h (bottom ∙h p) ~ top ∙h (right ∙h p)).
   ```

3. Splicing a homotopy `p : h ~ u` and its inverse into the middle gives a
   commuting square of homotopies

   ```text
                      top
              f --------------> g
              |                 |
    left ∙h p |                 | right
              ∨                 ∨
              u --------------> i.
                 p⁻¹ ∙h bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((left ∙h p) ∙h (p⁻¹ ∙h bottom) ~ top ∙h right).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ ((left ∙h p⁻¹) ∙h (p ∙h bottom) ~ top ∙h right).
   ```

4. Splicing a homotopy `p : g ~ u` and its inverse into the middle gives a
   commuting square of homotopies

   ```text
             top ∙h p
          f --------> u
          |           |
     left |           | p⁻¹ ∙h right
          ∨           ∨
          h --------> i.
             bottom
   ```

   More precisely, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h bottom ~ (top ∙h p) ∙h (p⁻¹ ∙h right)).
   ```

   Similarly, we have an equivalence

   ```text
     (left ∙h bottom ~ top ∙h right) ≃ (left ∙h bottom ~ (top ∙h p⁻¹) ∙h (p ∙h right)).
   ```

These operations are useful in proofs involving homotopy algebra, because taking
`equiv-right-whisker-concat-coherence-square-homotopies` as an example, it
provides us with two maps: the forward direction states
`(p ∙h r ~ q ∙h s) → (p ∙h (r ∙h t)) ~ q ∙h (s ∙h t))`, which allows one to
append a homotopy without needing to reassociate on the right, and the backwards
direction conversely allows one to cancel out a homotopy in parentheses.

#### Left whiskering coherences of commuting squares of homotopies

For any homotopy `p : u ~ f` we obtain an equivalence

```text
           top                                p ∙h top
       f -------> g                         u -------> g
       |          |                         |          |
  left |          | right    ≃    p ∙h left |          | right
       ∨          ∨                         ∨          ∨
       h -------> i                         h -------> i
          bottom                               bottom
```

of coherences of commuting squares of homotopies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i u : (x : A) → B x}
  where

  equiv-left-whisker-concat-coherence-square-homotopies :
    (p : u ~ f)
    (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i) →
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies (p ∙h top) (p ∙h left) right bottom
  equiv-left-whisker-concat-coherence-square-homotopies
    p top left right bottom =
    equiv-Π-equiv-family
      ( λ x →
        equiv-left-whisker-concat-coherence-square-identifications
          ( p x) (top x) (left x) (right x) (bottom x))
```

#### Right whiskering coherences of commuting squares of homotopies

For any homotopy `p : i ~ u` we obtain an equivalence

```text
           top                                 top
       f -------> g                     f ------------> g
       |          |                     |               |
  left |          | right    ≃     left |               | right ∙h p
       ∨          ∨                     ∨               ∨
       h -------> i                     h ------------> i
          bottom                           bottom ∙h p
```

of coherences of commuting squares of homotopies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  equiv-right-whisker-concat-coherence-square-homotopies :
    {u : (x : A) → B x} (p : i ~ u) →
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top left (right ∙h p) (bottom ∙h p)
  equiv-right-whisker-concat-coherence-square-homotopies p =
    equiv-Π-equiv-family
      ( λ x →
        equiv-right-whisker-concat-coherence-square-identifications
          ( top x) (left x) (right x) (bottom x) (p x))
```

#### Left splicing coherences of commuting squares of homotopies

For any inverse pair of homotopies `p : g ~ u` and `q : u ~ g` equipped with
`α : inv-htpy p ~ q` we obtain an equivalence

```text
           top                                    top
       f -------> g                         f -----------> g
       |          |                         |              |
  left |          | right    ≃     left ∙h p |              | right
       ∨          ∨                         ∨              ∨
       h -------> i                         u -----------> i
          bottom                               q ∙h bottom
```

of coherences of commuting squares of homotopies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  equiv-left-splice-coherence-square-homotopies :
    {u : (x : A) → B x} (p : h ~ u) (q : u ~ h) (α : inv-htpy p ~ q) →
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies top (left ∙h p) right (q ∙h bottom)
  equiv-left-splice-coherence-square-homotopies p q α =
    equiv-Π-equiv-family
      ( λ x →
        equiv-left-splice-coherence-square-identifications
          ( top x) (left x) (right x) (bottom x) (p x) (q x) (α x))
```

#### Right splicing coherences of commuting squares of homotopies

For any inverse pair of homotopies `p : g ~ u` and `q : u ~ g` equipped with
`α : inv-htpy p ~ q` we obtain an equivalence

```text
           top                             top ∙h p
       f -------> g                     f --------> u
       |          |                     |           |
  left |          | right    ≃     left |           | q ∙h right
       ∨          ∨                     ∨           ∨
       h -------> i                     h --------> i
          bottom                           bottom
```

of coherences of commuting squares of homotopies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  equiv-right-splice-coherence-square-homotopies :
    {u : (x : A) → B x} (p : g ~ u) (q : u ~ g) (α : inv-htpy p ~ q) →
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies (top ∙h p) left (inv-htpy p ∙h right) bottom
  equiv-right-splice-coherence-square-homotopies p q α =
    equiv-Π-equiv-family
      ( λ x →
        equiv-right-splice-coherence-square-identifications
          ( top x) (left x) (right x) (bottom x) (p x) (q x) (α x))
```

### Double whiskering of commuting squares of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h u v i : (x : A) → B x}
  where

  equiv-double-whisker-coherence-square-homotopies :
    (p : f ~ g)
    (top : g ~ u) (left : g ~ h) (right : u ~ v) (bottom : h ~ v)
    (s : v ~ i) →
    coherence-square-homotopies top left right bottom ≃
    coherence-square-homotopies
      ( p ∙h top)
      ( p ∙h left)
      ( right ∙h s)
      ( bottom ∙h s)
  equiv-double-whisker-coherence-square-homotopies p top left right bottom q =
    equiv-Π-equiv-family
      ( λ x →
        equiv-double-whisker-coherence-square-identifications
          ( p x) (top x) (left x) (right x) (bottom x) (q x))
```

### Computing the pasting of two squares with `refl-htpy` on opposite sides

Consider two squares of homotopies as in the diagram

```text
                 refl-htpy
              a ----------> a
              |             |
     top-left |             | top-right
              ∨  refl-htpy  ∨
              b ----------> b
              |             |
  bottom-left |             | bottom-right
              ∨             ∨
              c ----------> c
                 refl-htpy
```

The result of vertically pasting these squares can be computed in terms of the
horizontal concatenation of homotopies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a b c : (x : A) → B x}
  (top-left : a ~ b) (top-right : a ~ b)
  (bottom-left : b ~ c) (bottom-right : b ~ c)
  where

  vertical-pasting-coherence-square-homotopies-horizontal-refl :
    (H : top-left ~ top-right) (K : bottom-left ~ bottom-right) →
    ( inv-coherence-square-homotopies-horizontal-refl
      ( top-left ∙h bottom-left)
      ( top-right ∙h bottom-right)
      ( vertical-pasting-coherence-square-homotopies
        ( refl-htpy)
        ( top-left)
        ( top-right)
        ( refl-htpy)
        ( bottom-left)
        ( bottom-right)
        ( refl-htpy)
        ( coherence-square-homotopies-horizontal-refl
          ( top-left)
          ( top-right)
          ( H))
        ( coherence-square-homotopies-horizontal-refl
          ( bottom-left)
          ( bottom-right)
          ( K)))) ~
    ( horizontal-concat-htpy² H K)
  vertical-pasting-coherence-square-homotopies-horizontal-refl H K x =
    vertical-pasting-coherence-square-identifications-horizontal-refl
      ( top-left x)
      ( top-right x)
      ( bottom-left x)
      ( bottom-right x)
      ( H x)
      ( K x)

  vertical-pasting-inv-coherence-square-homotopies-horizontal-refl :
    (H : coherence-square-homotopies
      ( refl-htpy)
      ( top-left)
      ( top-right)
      ( refl-htpy))
    (K : coherence-square-homotopies
      ( refl-htpy)
      ( bottom-left)
      ( bottom-right)
      ( refl-htpy)) →
    ( inv-coherence-square-homotopies-horizontal-refl
      ( top-left ∙h bottom-left)
      ( top-right ∙h bottom-right)
      ( vertical-pasting-coherence-square-homotopies
        ( refl-htpy)
        ( top-left)
        ( top-right)
        ( refl-htpy)
        ( bottom-left)
        ( bottom-right)
        ( refl-htpy)
        ( H)
        ( K))) ~
    ( horizontal-concat-htpy²
      ( inv-coherence-square-homotopies-horizontal-refl
        ( top-left)
        ( top-right)
        ( H))
      ( inv-coherence-square-homotopies-horizontal-refl
        ( bottom-left)
        ( bottom-right)
        ( K)))
  vertical-pasting-inv-coherence-square-homotopies-horizontal-refl H K x =
    vertical-pasting-inv-coherence-square-identifications-horizontal-refl
      ( top-left x)
      ( top-right x)
      ( bottom-left x)
      ( bottom-right x)
      ( H x)
      ( K x)
```
