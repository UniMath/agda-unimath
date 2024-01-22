# Extensions of span diagrams

```agda
module foundation.extensions-span-diagrams where

open import foundation-core.extensions-span-diagrams public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.extensions-spans
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "extension" Disambiguation="span diagram"}} of `𝒮` by `i` and `j` is
the span diagram

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B.
```

## Definitions

#### Extensions of span diagrams by equivalences of arrows on the left

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow f' f` as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |    ≃    |
  f' |       f |
     V    ≃    V
     A' -----> A'.
          h₁
```

Then we obtain a span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : equiv-arrow f' (left-map-span-diagram 𝒮))
  where

  domain-left-extend-equiv-arrow-span-diagram : UU l5
  domain-left-extend-equiv-arrow-span-diagram = A'

  codomain-left-extend-equiv-arrow-span-diagram : UU l2
  codomain-left-extend-equiv-arrow-span-diagram = codomain-span-diagram 𝒮

  span-left-extend-equiv-arrow-span-diagram :
    span l4
      ( domain-left-extend-equiv-arrow-span-diagram)
      ( codomain-left-extend-equiv-arrow-span-diagram)
  span-left-extend-equiv-arrow-span-diagram =
    left-extend-equiv-arrow-span (span-span-diagram 𝒮) f' h

  left-extend-equiv-arrow-span-diagram : span-diagram l5 l2 l4
  pr1 left-extend-equiv-arrow-span-diagram =
    domain-left-extend-equiv-arrow-span-diagram
  pr1 (pr2 left-extend-equiv-arrow-span-diagram) =
    codomain-left-extend-equiv-arrow-span-diagram
  pr2 (pr2 left-extend-equiv-arrow-span-diagram) =
    span-left-extend-equiv-arrow-span-diagram

  spanning-type-left-extend-equiv-arrow-span-diagram : UU l4
  spanning-type-left-extend-equiv-arrow-span-diagram =
    spanning-type-span-diagram left-extend-equiv-arrow-span-diagram

  left-map-left-extend-equiv-arrow-span-diagram :
    spanning-type-left-extend-equiv-arrow-span-diagram →
    domain-left-extend-equiv-arrow-span-diagram
  left-map-left-extend-equiv-arrow-span-diagram =
    left-map-span-diagram left-extend-equiv-arrow-span-diagram

  right-map-left-extend-equiv-arrow-span-diagram :
    spanning-type-left-extend-equiv-arrow-span-diagram →
    codomain-left-extend-equiv-arrow-span-diagram
  right-map-left-extend-equiv-arrow-span-diagram =
    right-map-span-diagram left-extend-equiv-arrow-span-diagram
```

#### Extensions of span diagrams by equivalences of arrows on the left

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow g' g` as indicated in the diagram

```text
         g'
     S' ----> B'
     |        |
  h₀ | ≃    ≃ | h₁
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
  (h : equiv-arrow g' (right-map-span-diagram 𝒮))
  where

  domain-right-extend-equiv-arrow-span-diagram : UU l1
  domain-right-extend-equiv-arrow-span-diagram = domain-span-diagram 𝒮

  codomain-right-extend-equiv-arrow-span-diagram : UU l5
  codomain-right-extend-equiv-arrow-span-diagram = B'

  span-right-extend-equiv-arrow-span-diagram :
    span l4
      ( domain-right-extend-equiv-arrow-span-diagram)
      ( codomain-right-extend-equiv-arrow-span-diagram)
  span-right-extend-equiv-arrow-span-diagram =
    right-extend-equiv-arrow-span (span-span-diagram 𝒮) g' h

  right-extend-equiv-arrow-span-diagram : span-diagram l1 l5 l4
  pr1 right-extend-equiv-arrow-span-diagram =
    domain-right-extend-equiv-arrow-span-diagram
  pr1 (pr2 right-extend-equiv-arrow-span-diagram) =
    codomain-right-extend-equiv-arrow-span-diagram
  pr2 (pr2 right-extend-equiv-arrow-span-diagram) =
    span-right-extend-equiv-arrow-span-diagram

  spanning-type-right-extend-equiv-arrow-span-diagram : UU l4
  spanning-type-right-extend-equiv-arrow-span-diagram =
    spanning-type-span-diagram right-extend-equiv-arrow-span-diagram

  left-map-right-extend-equiv-arrow-span-diagram :
    spanning-type-right-extend-equiv-arrow-span-diagram →
    domain-right-extend-equiv-arrow-span-diagram
  left-map-right-extend-equiv-arrow-span-diagram =
    left-map-span-diagram right-extend-equiv-arrow-span-diagram

  right-map-right-extend-equiv-arrow-span-diagram :
    spanning-type-right-extend-equiv-arrow-span-diagram →
    codomain-right-extend-equiv-arrow-span-diagram
  right-map-right-extend-equiv-arrow-span-diagram =
    right-map-span-diagram right-extend-equiv-arrow-span-diagram
```
