# Commuting squares of homotopies

```agda
module foundation.commuting-squares-of-homotopies where

open import foundation-core.commuting-squares-of-homotopies public
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-identifications
open import foundation.functoriality-dependent-function-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalences
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

### Right whiskering a commuting square of homotopies with respect to concatenation of homotopies

Consider a
[commuting square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      v         v
      h ------> i
        bottom
```

and consider a homotopy `H : i ~ j`. Then there is an equivalence of commuting
squares of homotopies

```text
          top                               top
      f ------> g                    f -------------> g
      |         |                    |                |
 left |         | right    ≃    left |                | right ∙h H
      ∨         ∨                    ∨                ∨
      h ------> i                    h -------------> j
        bottom                          bottom ∙h H
```

This is the
{{#concept "right whiskering" Disambiguation="commuting squares of homotopies with respect to concatenation" Agda=right-whisker-concat-coherence-square-homotopies}}
operation of commuting squares of homotopies with respect to concatenation.

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g g' h k : A → B}
  ( H : f ~ g) (H' : f ~ g') {K : g ~ h} {K' : g' ~ h} (L : h ~ k)
  where

  equiv-right-whisker-concat-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' ≃
    coherence-square-homotopies H H' (K ∙h L) (K' ∙h L)
  equiv-right-whisker-concat-coherence-square-homotopies =
    equiv-Π-equiv-family
      ( λ a →
        equiv-right-whisker-concat-coherence-square-identifications
          ( H a)
          ( H' a)
          ( K a)
          ( K' a)
          ( L a))

  right-whisker-concat-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies H H' (K ∙h L) (K' ∙h L)
  right-whisker-concat-coherence-square-homotopies =
    map-equiv equiv-right-whisker-concat-coherence-square-homotopies

  right-unwhisker-concat-htpy-coherence-square-homotopies :
    coherence-square-homotopies H H' (K ∙h L) (K' ∙h L) →
    coherence-square-homotopies H H' K K'
  right-unwhisker-concat-htpy-coherence-square-homotopies =
    map-inv-equiv equiv-right-whisker-concat-coherence-square-homotopies
```

### Left whiskering a commuting square of homotopies with respect to concatenation of homotopies

Consider a
[commuting square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      v         v
      h ------> i
        bottom
```

and consider a homotopy `H : e ~ f`. Then there is an equivalence of commuting
squares of homotopies

```text
          top                                H ∙h top
      f ------> g                         e ----------> g
      |         |                         |             |
 left |         | right    ≃    H ∙h left |             | right
      ∨         ∨                         ∨             ∨
      h ------> i                         h ----------> i
        bottom                                bottom
```

This is the
{{#concept "left whiskering" Disambiguation="commuting squares of homotopies with respect to concatenation" Agda=left-whisker-concat-coherence-square-homotopies}}
operation of commuting squares of homotopies with respect to concatenation.

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g g' h k : A → B}
  ( L : k ~ f) {H : f ~ g} {H' : f ~ g'} {K : g ~ h} {K' : g' ~ h}
  where

  equiv-left-whisker-concat-coherence-square-homotopies :
    ( coherence-square-homotopies H H' K K') ≃
    ( coherence-square-homotopies (L ∙h H) (L ∙h H') K K')
  equiv-left-whisker-concat-coherence-square-homotopies =
    equiv-Π-equiv-family
      ( λ a →
        equiv-left-whisker-concat-coherence-square-identifications
          ( L a)
          ( H a)
          ( H' a)
          ( K a)
          ( K' a))

  left-whisker-concat-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (L ∙h H) (L ∙h H') K K'
  left-whisker-concat-coherence-square-homotopies =
    map-equiv equiv-left-whisker-concat-coherence-square-homotopies

  left-unwhisker-concat-htpy-coherence-square-homotopies :
    coherence-square-homotopies (L ∙h H) (L ∙h H') K K' →
    coherence-square-homotopies H H' K K'
  left-unwhisker-concat-htpy-coherence-square-homotopies =
    map-inv-equiv equiv-left-whisker-concat-coherence-square-homotopies
```

### Left whiskering a commuting square of homotopies with respect to concatenation of homotopies

Consider a
[commuting square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      v         v
      h ------> i
        bottom
```

and consider a homotopy `H : e ~ f`. Then there is an equivalence of commuting
squares of homotopies

```text
          top                                H ∙h top
      f ------> g                         e ----------> g
      |         |                         |             |
 left |         | right    ≃    H ∙h left |             | right
      ∨         ∨                         ∨             ∨
      h ------> i                         h ----------> i
        bottom                                bottom
```

This is the
{{#concept "double whiskering" Disambiguation="commuting squares of homotopies with respect to concatenation" Agda=double-whisker-coherence-square-homotopies}}
operation of commuting squares of homotopies with respect to concatenation.

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  { f g h h' k m : A → B}
  ( H : f ~ g) {K : g ~ h} {K' : g ~ h'} {L : h ~ k} {L' : h' ~ k} (M : k ~ m)
  where

  equiv-double-whisker-coherence-square-homotopies :
    ( coherence-square-homotopies K K' L L') ≃
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  equiv-double-whisker-coherence-square-homotopies =
    equiv-Π-equiv-family
      ( λ a →
        equiv-double-whisker-square-identifications
          ( H a)
          ( K a)
          ( K' a)
          ( L a)
          ( L' a)
          ( M a))

  double-whisker-coherence-square-homotopies :
    ( coherence-square-homotopies K K' L L') →
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M))
  double-whisker-coherence-square-homotopies =
    map-equiv equiv-double-whisker-coherence-square-homotopies

  double-unwhisker-concat-htpy-coherence-square-homotopies :
    ( coherence-square-homotopies (H ∙h K) (H ∙h K') (L ∙h M) (L' ∙h M)) →
    ( coherence-square-homotopies K K' L L')
  double-unwhisker-concat-htpy-coherence-square-homotopies =
    map-inv-equiv equiv-double-whisker-coherence-square-homotopies
```

### Whiskering a square of homotopies by a map

Given a square of homotopies

```text
        H
    g -----> h
    |        |
 H' |   ⇗    | K
    ∨        ∨
   h' -----> k
        K'
```

and a map `f`, we may whisker it by a map on the left into a square of
homotopies

```text
             f ·l H
         fg --------> fh
         |            |
 f ·l H' |      ⇗     |f ·l K
         ∨            ∨
        fh' --------> fk,
             f ·l K'
```

and similarly we may whisker it on the right.

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  ( f : B → C) {g h h' k : A → B}
  ( H : g ~ h) (H' : g ~ h') {K : h ~ k} {K' : h' ~ k}
  where

  map-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (f ·l H) (f ·l H') (f ·l K) (f ·l K')
  map-coherence-square-homotopies α a =
    map-coherence-square-identifications f (H a) (H' a) (K a) (K' a) (α a)

module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  { g h h' k : B → C} (H : g ~ h) (H' : g ~ h') {K : h ~ k} {K' : h' ~ k}
  ( f : A → B)
  where

  right-whisker-comp-coherence-square-homotopies :
    coherence-square-homotopies H H' K K' →
    coherence-square-homotopies (H ·r f) (H' ·r f) (K ·r f) (K' ·r f)
  right-whisker-comp-coherence-square-homotopies α = α ·r f
```
