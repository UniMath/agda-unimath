# Operations on span diagrams

```agda
module foundation-core.operations-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.operations-spans
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains some operations on
[span diagrams](foundation.span-diagrams.md) that produce new span diagrams from
given span diagrams and possibly other data.

## Definitions

### Concatenating span diagrams and maps on both sides

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "concatenation-span-diagram" Disambiguation="span diagram" Agda=concat-span-diagram}}
of `𝒮`, `i`, and `j` is the span diagram

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B'.
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  where

  concat-span-diagram :
    (𝒮 : span-diagram l1 l2 l3)
    {A' : UU l4} (i : domain-span-diagram 𝒮 → A')
    {B' : UU l5} (j : codomain-span-diagram 𝒮 → B') →
    span-diagram l4 l5 l3
  pr1 (concat-span-diagram 𝒮 {A'} i {B'} j) =
    A'
  pr1 (pr2 (concat-span-diagram 𝒮 {A'} i {B'} j)) =
    B'
  pr2 (pr2 (concat-span-diagram 𝒮 {A'} i {B'} j)) =
    concat-span (span-span-diagram 𝒮) i j
```

### Concatenating span diagrams and maps on the left

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a map `i : A → A'`. The
{{#concept "left concatenation" Disambiguation="span diagram" Agda=left-concat-span-diagram}}
of `𝒮` and `i` is the span diagram

```text
       i ∘ f      g
  A' <------- S -----> B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  left-concat-span-diagram :
    (𝒮 : span-diagram l1 l2 l3) {A' : UU l4} →
    (domain-span-diagram 𝒮 → A') → span-diagram l4 l2 l3
  left-concat-span-diagram 𝒮 f = concat-span-diagram 𝒮 f id
```

### Concatenating span diagrams and maps on the right

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a map `j : B → B'`. The
{{#concept "right concatenation" Disambiguation="span diagram" Agda=right-concat-span-diagram}}
of `𝒮` by `j` is the span diagram

```text
        f      j ∘ g
  A' <----- S -------> B'.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  right-concat-span-diagram :
    (𝒮 : span-diagram l1 l2 l3) {B' : UU l4} →
    (codomain-span-diagram 𝒮 → B') → span-diagram l1 l4 l3
  right-concat-span-diagram 𝒮 g = concat-span-diagram 𝒮 id g
```

### Concatenation of span diagrams and morphisms of arrows on the left

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f`
as indicated in the diagram

```text
          f'
     A' <---- S'
     |        |
  h₀ |        | h₁
     ∨        ∨
     A <----- S -----> B.
          f       g
```

Then we obtain a span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : hom-arrow f' (left-map-span-diagram 𝒮))
  where

  domain-left-concat-hom-arrow-span-diagram : UU l5
  domain-left-concat-hom-arrow-span-diagram = A'

  codomain-left-concat-hom-arrow-span-diagram : UU l2
  codomain-left-concat-hom-arrow-span-diagram = codomain-span-diagram 𝒮

  span-left-concat-hom-arrow-span-diagram :
    span l4
      ( domain-left-concat-hom-arrow-span-diagram)
      ( codomain-left-concat-hom-arrow-span-diagram)
  span-left-concat-hom-arrow-span-diagram =
    left-concat-hom-arrow-span
      ( span-span-diagram 𝒮)
      ( f')
      ( h)

  left-concat-hom-arrow-span-diagram : span-diagram l5 l2 l4
  pr1 left-concat-hom-arrow-span-diagram =
    domain-left-concat-hom-arrow-span-diagram
  pr1 (pr2 left-concat-hom-arrow-span-diagram) =
    codomain-left-concat-hom-arrow-span-diagram
  pr2 (pr2 left-concat-hom-arrow-span-diagram) =
    span-left-concat-hom-arrow-span-diagram

  spanning-type-left-concat-hom-arrow-span-diagram : UU l4
  spanning-type-left-concat-hom-arrow-span-diagram =
    spanning-type-span-diagram left-concat-hom-arrow-span-diagram

  left-map-left-concat-hom-arrow-span-diagram :
    spanning-type-left-concat-hom-arrow-span-diagram →
    domain-left-concat-hom-arrow-span-diagram
  left-map-left-concat-hom-arrow-span-diagram =
    left-map-span-diagram left-concat-hom-arrow-span-diagram

  right-map-left-concat-hom-arrow-span-diagram :
    spanning-type-left-concat-hom-arrow-span-diagram →
    codomain-left-concat-hom-arrow-span-diagram
  right-map-left-concat-hom-arrow-span-diagram =
    right-map-span-diagram left-concat-hom-arrow-span-diagram
```

### Concatenation of span diagrams and morphisms of arrows on the right

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow g' g`
as indicated in the diagram

```text
               g'
           S' ----> B'
           |        |
        h₀ |        | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span diagram `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span-diagram 𝒮))
  where

  domain-right-concat-hom-arrow-span-diagram : UU l1
  domain-right-concat-hom-arrow-span-diagram = domain-span-diagram 𝒮

  codomain-right-concat-hom-arrow-span-diagram : UU l5
  codomain-right-concat-hom-arrow-span-diagram = B'

  span-right-concat-hom-arrow-span-diagram :
    span l4
      ( domain-right-concat-hom-arrow-span-diagram)
      ( codomain-right-concat-hom-arrow-span-diagram)
  span-right-concat-hom-arrow-span-diagram =
    right-concat-hom-arrow-span
      ( span-span-diagram 𝒮)
      ( g')
      ( h)

  right-concat-hom-arrow-span-diagram : span-diagram l1 l5 l4
  pr1 right-concat-hom-arrow-span-diagram =
    domain-right-concat-hom-arrow-span-diagram
  pr1 (pr2 right-concat-hom-arrow-span-diagram) =
    codomain-right-concat-hom-arrow-span-diagram
  pr2 (pr2 right-concat-hom-arrow-span-diagram) =
    span-right-concat-hom-arrow-span-diagram

  spanning-type-right-concat-hom-arrow-span-diagram : UU l4
  spanning-type-right-concat-hom-arrow-span-diagram =
    spanning-type-span-diagram right-concat-hom-arrow-span-diagram

  left-map-right-concat-hom-arrow-span-diagram :
    spanning-type-right-concat-hom-arrow-span-diagram →
    domain-right-concat-hom-arrow-span-diagram
  left-map-right-concat-hom-arrow-span-diagram =
    left-map-span-diagram right-concat-hom-arrow-span-diagram

  right-map-right-concat-hom-arrow-span-diagram :
    spanning-type-right-concat-hom-arrow-span-diagram →
    codomain-right-concat-hom-arrow-span-diagram
  right-map-right-concat-hom-arrow-span-diagram =
    right-map-span-diagram right-concat-hom-arrow-span-diagram
```
