# Operations on span diagrams

```agda
module foundation.operations-span-diagrams where

open import foundation-core.operations-span-diagrams public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.operations-spans
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.equivalences-arrows
```

</details>

## Idea

This file contains some further operations on
[span diagrams](foundation.span-diagrams.md) that produce new span diagrams from
given span diagrams and possibly other data. Previous operations on span
diagrams were defined in
[`foundation-core.operations-span-diagrams`](foundation-core.operations-span-diagrams.md).

## Definitions

### Concatenating span diagrams and equivalences of arrows on the left

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation-core.equivalences-arrows.md)
`h : equiv-arrow f' f` as indicated in the diagram

```text
          f'
     A' <---- S'
     |        |
  h₀ | ≃    ≃ | h₁
     ∨        ∨
     A <----- S -----> B.
          f       g
```

Then we obtain a span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : equiv-arrow f' (left-map-span-diagram 𝒮))
  where

  domain-left-concat-equiv-arrow-span-diagram : UU l5
  domain-left-concat-equiv-arrow-span-diagram = A'

  codomain-left-concat-equiv-arrow-span-diagram : UU l2
  codomain-left-concat-equiv-arrow-span-diagram = codomain-span-diagram 𝒮

  span-left-concat-equiv-arrow-span-diagram :
    span l4
      ( domain-left-concat-equiv-arrow-span-diagram)
      ( codomain-left-concat-equiv-arrow-span-diagram)
  span-left-concat-equiv-arrow-span-diagram =
    left-concat-equiv-arrow-span (span-span-diagram 𝒮) f' h

  left-concat-equiv-arrow-span-diagram : span-diagram l5 l2 l4
  pr1 left-concat-equiv-arrow-span-diagram =
    domain-left-concat-equiv-arrow-span-diagram
  pr1 (pr2 left-concat-equiv-arrow-span-diagram) =
    codomain-left-concat-equiv-arrow-span-diagram
  pr2 (pr2 left-concat-equiv-arrow-span-diagram) =
    span-left-concat-equiv-arrow-span-diagram

  spanning-type-left-concat-equiv-arrow-span-diagram : UU l4
  spanning-type-left-concat-equiv-arrow-span-diagram =
    spanning-type-span-diagram left-concat-equiv-arrow-span-diagram

  left-map-left-concat-equiv-arrow-span-diagram :
    spanning-type-left-concat-equiv-arrow-span-diagram →
    domain-left-concat-equiv-arrow-span-diagram
  left-map-left-concat-equiv-arrow-span-diagram =
    left-map-span-diagram left-concat-equiv-arrow-span-diagram

  right-map-left-concat-equiv-arrow-span-diagram :
    spanning-type-left-concat-equiv-arrow-span-diagram →
    codomain-left-concat-equiv-arrow-span-diagram
  right-map-left-concat-equiv-arrow-span-diagram =
    right-map-span-diagram left-concat-equiv-arrow-span-diagram
```

### Concatenating span diagrams and equivalences of arrows on the right

Consider a span diagram `𝒮` given by

```text
       f       g
  A <----- S -----> B
```

and a [equivalence of arrows](foundation-core.equivalences-arrows.md)
`h : equiv-arrow g' g` as indicated in the diagram

```text
               g'
           S' ----> B'
           |        |
        h₀ | ≃    ≃ | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span diagram `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : equiv-arrow g' (right-map-span-diagram 𝒮))
  where

  domain-right-concat-equiv-arrow-span-diagram : UU l1
  domain-right-concat-equiv-arrow-span-diagram = domain-span-diagram 𝒮

  codomain-right-concat-equiv-arrow-span-diagram : UU l5
  codomain-right-concat-equiv-arrow-span-diagram = B'

  span-right-concat-equiv-arrow-span-diagram :
    span l4
      ( domain-right-concat-equiv-arrow-span-diagram)
      ( codomain-right-concat-equiv-arrow-span-diagram)
  span-right-concat-equiv-arrow-span-diagram =
    right-concat-equiv-arrow-span (span-span-diagram 𝒮) g' h

  right-concat-equiv-arrow-span-diagram : span-diagram l1 l5 l4
  pr1 right-concat-equiv-arrow-span-diagram =
    domain-right-concat-equiv-arrow-span-diagram
  pr1 (pr2 right-concat-equiv-arrow-span-diagram) =
    codomain-right-concat-equiv-arrow-span-diagram
  pr2 (pr2 right-concat-equiv-arrow-span-diagram) =
    span-right-concat-equiv-arrow-span-diagram

  spanning-type-right-concat-equiv-arrow-span-diagram : UU l4
  spanning-type-right-concat-equiv-arrow-span-diagram =
    spanning-type-span-diagram right-concat-equiv-arrow-span-diagram

  left-map-right-concat-equiv-arrow-span-diagram :
    spanning-type-right-concat-equiv-arrow-span-diagram →
    domain-right-concat-equiv-arrow-span-diagram
  left-map-right-concat-equiv-arrow-span-diagram =
    left-map-span-diagram right-concat-equiv-arrow-span-diagram

  right-map-right-concat-equiv-arrow-span-diagram :
    spanning-type-right-concat-equiv-arrow-span-diagram →
    codomain-right-concat-equiv-arrow-span-diagram
  right-map-right-concat-equiv-arrow-span-diagram =
    right-map-span-diagram right-concat-equiv-arrow-span-diagram
```
