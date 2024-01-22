# Extensions of span diagrams

```agda
module foundation-core.extensions-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.extensions-spans
open import foundation.morphisms-arrows
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "extension" Disambiguation="span diagram" Agda=extend-span-diagram}}
of `𝒮` by `i` and `j` is the span diagram

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B'.
```

## Definitions

### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  where

  extend-span-diagram :
    (𝒮 : span-diagram l1 l2 l3)
    {A' : UU l4} (f : domain-span-diagram 𝒮 → A')
    {B' : UU l5} (g : codomain-span-diagram 𝒮 → B') →
    span-diagram l4 l5 l3
  pr1 (extend-span-diagram 𝒮 {A'} f {B'} g) =
    A'
  pr1 (pr2 (extend-span-diagram 𝒮 {A'} f {B'} g)) =
    B'
  pr2 (pr2 (extend-span-diagram 𝒮 {A'} f {B'} g)) =
    extend-span (span-span-diagram 𝒮) f g
```

### Extensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  left-extend-span-diagram :
    (𝒮 : span-diagram l1 l2 l3) {A' : UU l4} →
    (domain-span-diagram 𝒮 → A') → span-diagram l4 l2 l3
  left-extend-span-diagram 𝒮 f = extend-span-diagram 𝒮 f id
```

### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  right-extend-span-diagram :
    (𝒮 : span-diagram l1 l2 l3) {B' : UU l4} →
    (codomain-span-diagram 𝒮 → B') → span-diagram l1 l4 l3
  right-extend-span-diagram 𝒮 g = extend-span-diagram 𝒮 id g
```

### Extensions by morphisms of arrows on the left

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f`
as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |
  f' |       f |
     V         V
     A' -----> A.
          h₁
```

Then we obtain a span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : hom-arrow f' (left-map-span-diagram 𝒮))
  where

  domain-left-extend-hom-arrow-span-diagram : UU l5
  domain-left-extend-hom-arrow-span-diagram = A'

  codomain-left-extend-hom-arrow-span-diagram : UU l2
  codomain-left-extend-hom-arrow-span-diagram = codomain-span-diagram 𝒮

  span-left-extend-hom-arrow-span-diagram :
    span l4
      ( domain-left-extend-hom-arrow-span-diagram)
      ( codomain-left-extend-hom-arrow-span-diagram)
  span-left-extend-hom-arrow-span-diagram =
    left-extend-hom-arrow-span
      ( span-span-diagram 𝒮)
      ( f')
      ( h)

  left-extend-hom-arrow-span-diagram : span-diagram l5 l2 l4
  pr1 left-extend-hom-arrow-span-diagram =
    domain-left-extend-hom-arrow-span-diagram
  pr1 (pr2 left-extend-hom-arrow-span-diagram) =
    codomain-left-extend-hom-arrow-span-diagram
  pr2 (pr2 left-extend-hom-arrow-span-diagram) =
    span-left-extend-hom-arrow-span-diagram

  spanning-type-left-extend-hom-arrow-span-diagram : UU l4
  spanning-type-left-extend-hom-arrow-span-diagram =
    spanning-type-span-diagram left-extend-hom-arrow-span-diagram

  left-map-left-extend-hom-arrow-span-diagram :
    spanning-type-left-extend-hom-arrow-span-diagram →
    domain-left-extend-hom-arrow-span-diagram
  left-map-left-extend-hom-arrow-span-diagram =
    left-map-span-diagram left-extend-hom-arrow-span-diagram

  right-map-left-extend-hom-arrow-span-diagram :
    spanning-type-left-extend-hom-arrow-span-diagram →
    codomain-left-extend-hom-arrow-span-diagram
  right-map-left-extend-hom-arrow-span-diagram =
    right-map-span-diagram left-extend-hom-arrow-span-diagram
```

### Extensions by morphisms of arrows on the left

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
     V        V
     S -----> B
     |   g
   f |
     V
     A.
```

Then we obtain a span diagram `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span-diagram 𝒮))
  where

  domain-right-extend-hom-arrow-span-diagram : UU l1
  domain-right-extend-hom-arrow-span-diagram = domain-span-diagram 𝒮

  codomain-right-extend-hom-arrow-span-diagram : UU l5
  codomain-right-extend-hom-arrow-span-diagram = B'

  span-right-extend-hom-arrow-span-diagram :
    span l4
      ( domain-right-extend-hom-arrow-span-diagram)
      ( codomain-right-extend-hom-arrow-span-diagram)
  span-right-extend-hom-arrow-span-diagram =
    right-extend-hom-arrow-span
      ( span-span-diagram 𝒮)
      ( g')
      ( h)

  right-extend-hom-arrow-span-diagram : span-diagram l1 l5 l4
  pr1 right-extend-hom-arrow-span-diagram =
    domain-right-extend-hom-arrow-span-diagram
  pr1 (pr2 right-extend-hom-arrow-span-diagram) =
    codomain-right-extend-hom-arrow-span-diagram
  pr2 (pr2 right-extend-hom-arrow-span-diagram) =
    span-right-extend-hom-arrow-span-diagram

  spanning-type-right-extend-hom-arrow-span-diagram : UU l4
  spanning-type-right-extend-hom-arrow-span-diagram =
    spanning-type-span-diagram right-extend-hom-arrow-span-diagram

  left-map-right-extend-hom-arrow-span-diagram :
    spanning-type-right-extend-hom-arrow-span-diagram →
    domain-right-extend-hom-arrow-span-diagram
  left-map-right-extend-hom-arrow-span-diagram =
    left-map-span-diagram right-extend-hom-arrow-span-diagram

  right-map-right-extend-hom-arrow-span-diagram :
    spanning-type-right-extend-hom-arrow-span-diagram →
    codomain-right-extend-hom-arrow-span-diagram
  right-map-right-extend-hom-arrow-span-diagram =
    right-map-span-diagram right-extend-hom-arrow-span-diagram
```
