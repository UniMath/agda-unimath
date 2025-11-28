# Operations on cospan diagrams

```agda
module foundation.operations-cospan-diagrams where

open import foundation-core.operations-cospan-diagrams public
```

<details><summary>Imports</summary>

```agda
open import foundation.cospan-diagrams
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.operations-cospans
open import foundation.universe-levels
```

</details>

## Idea

This file contains some further operations on
[cospan diagrams](foundation.cospan-diagrams.md) that produce new cospan
diagrams from given cospan diagrams and possibly other data. Previous operations
on cospan diagrams were defined in
[`foundation-core.operations-cospan-diagrams`](foundation-core.operations-cospan-diagrams.md).

## Definitions

### Concatenating cospan diagrams and equivalences of arrows on the left

Consider a cospan diagram `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and an [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow f' f` as indicated in the diagram

```text
          f         g
     A ------> S <------ B.
     |         |
  h₀ | ≃     ≃ | h₁
     ∨         ∨
     A' -----> S'
          f'
```

Then we obtain a cospan diagram `A' --> S' <-- B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : A' → S')
  (h : equiv-arrow (left-map-cospan-diagram 𝒮) f')
  where

  domain-left-concat-equiv-arrow-cospan-diagram : UU l5
  domain-left-concat-equiv-arrow-cospan-diagram = A'

  codomain-left-concat-equiv-arrow-cospan-diagram : UU l2
  codomain-left-concat-equiv-arrow-cospan-diagram = codomain-cospan-diagram 𝒮

  cospan-left-concat-equiv-arrow-cospan-diagram :
    cospan l4
      ( domain-left-concat-equiv-arrow-cospan-diagram)
      ( codomain-left-concat-equiv-arrow-cospan-diagram)
  cospan-left-concat-equiv-arrow-cospan-diagram =
    left-concat-equiv-arrow-cospan (cospan-cospan-diagram 𝒮) f' h

  left-concat-equiv-arrow-cospan-diagram : cospan-diagram l5 l2 l4
  pr1 left-concat-equiv-arrow-cospan-diagram =
    domain-left-concat-equiv-arrow-cospan-diagram
  pr1 (pr2 left-concat-equiv-arrow-cospan-diagram) =
    codomain-left-concat-equiv-arrow-cospan-diagram
  pr2 (pr2 left-concat-equiv-arrow-cospan-diagram) =
    cospan-left-concat-equiv-arrow-cospan-diagram

  cospanning-type-left-concat-equiv-arrow-cospan-diagram : UU l4
  cospanning-type-left-concat-equiv-arrow-cospan-diagram =
    cospanning-type-cospan-diagram left-concat-equiv-arrow-cospan-diagram

  left-map-left-concat-equiv-arrow-cospan-diagram :
    domain-left-concat-equiv-arrow-cospan-diagram →
    cospanning-type-left-concat-equiv-arrow-cospan-diagram
  left-map-left-concat-equiv-arrow-cospan-diagram =
    left-map-cospan-diagram left-concat-equiv-arrow-cospan-diagram

  right-map-left-concat-equiv-arrow-cospan-diagram :
    codomain-left-concat-equiv-arrow-cospan-diagram →
    cospanning-type-left-concat-equiv-arrow-cospan-diagram
  right-map-left-concat-equiv-arrow-cospan-diagram =
    right-map-cospan-diagram left-concat-equiv-arrow-cospan-diagram
```

### Concatenating cospan diagrams and equivalences of arrows on the right

Consider a cospan diagram `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and a [equivalence of arrows](foundation.equivalences-arrows.md)
`h : equiv-arrow g' g` as indicated in the diagram

```text
       f         g
  A ------> S <------ B.
            |         |
         h₀ | ≃     ≃ | h₁
            ∨         ∨
            S' <----- B'
                 g'
```

Then we obtain a cospan diagram `A --> S' <-- B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : B' → S')
  (h : equiv-arrow (right-map-cospan-diagram 𝒮) g')
  where

  domain-right-concat-equiv-arrow-cospan-diagram : UU l1
  domain-right-concat-equiv-arrow-cospan-diagram = domain-cospan-diagram 𝒮

  codomain-right-concat-equiv-arrow-cospan-diagram : UU l5
  codomain-right-concat-equiv-arrow-cospan-diagram = B'

  cospan-right-concat-equiv-arrow-cospan-diagram :
    cospan l4
      ( domain-right-concat-equiv-arrow-cospan-diagram)
      ( codomain-right-concat-equiv-arrow-cospan-diagram)
  cospan-right-concat-equiv-arrow-cospan-diagram =
    right-concat-equiv-arrow-cospan (cospan-cospan-diagram 𝒮) g' h

  right-concat-equiv-arrow-cospan-diagram : cospan-diagram l1 l5 l4
  pr1 right-concat-equiv-arrow-cospan-diagram =
    domain-right-concat-equiv-arrow-cospan-diagram
  pr1 (pr2 right-concat-equiv-arrow-cospan-diagram) =
    codomain-right-concat-equiv-arrow-cospan-diagram
  pr2 (pr2 right-concat-equiv-arrow-cospan-diagram) =
    cospan-right-concat-equiv-arrow-cospan-diagram

  cospanning-type-right-concat-equiv-arrow-cospan-diagram : UU l4
  cospanning-type-right-concat-equiv-arrow-cospan-diagram =
    cospanning-type-cospan-diagram right-concat-equiv-arrow-cospan-diagram

  left-map-right-concat-equiv-arrow-cospan-diagram :
    domain-right-concat-equiv-arrow-cospan-diagram →
    cospanning-type-right-concat-equiv-arrow-cospan-diagram
  left-map-right-concat-equiv-arrow-cospan-diagram =
    left-map-cospan-diagram right-concat-equiv-arrow-cospan-diagram

  right-map-right-concat-equiv-arrow-cospan-diagram :
    codomain-right-concat-equiv-arrow-cospan-diagram →
    cospanning-type-right-concat-equiv-arrow-cospan-diagram
  right-map-right-concat-equiv-arrow-cospan-diagram =
    right-map-cospan-diagram right-concat-equiv-arrow-cospan-diagram
```
