# Operations on cospan diagrams

```agda
module foundation-core.operations-cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospan-diagrams
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.operations-cospans
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains some operations on
[cospan diagrams](foundation.cospan-diagrams.md) that produce new cospan
diagrams from given cospan diagrams and possibly other data.

## Definitions

### Concatenating cospan diagrams and maps on both sides

Consider a [cospan diagram](foundation.cospan-diagrams.md) `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and maps `i : A' → A` and `j : B' → B`. The
{{#concept "concatenation-cospan-diagram" Disambiguation="cospan diagram" Agda=concat-cospan-diagram}}
of `𝒮`, `i`, and `j` is the cospan diagram

```text
      f ∘ i     g ∘ j
  A' ------> S <------ B'.
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  where

  concat-cospan-diagram :
    (𝒮 : cospan-diagram l1 l2 l3)
    {A' : UU l4} (f : A' → domain-cospan-diagram 𝒮)
    {B' : UU l5} (g : B' → codomain-cospan-diagram 𝒮) →
    cospan-diagram l4 l5 l3
  pr1 (concat-cospan-diagram 𝒮 {A'} f {B'} g) =
    A'
  pr1 (pr2 (concat-cospan-diagram 𝒮 {A'} f {B'} g)) =
    B'
  pr2 (pr2 (concat-cospan-diagram 𝒮 {A'} f {B'} g)) =
    concat-cospan (cospan-cospan-diagram 𝒮) f g
```

### Concatenating cospan diagrams and maps on the left

Consider a [cospan diagram](foundation.cospan-diagrams.md) `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and a map `i : A' → A`. The
{{#concept "left concatenation" Disambiguation="cospan diagram" Agda=left-concat-cospan-diagram}}
of `𝒮` and `i` is the cospan diagram

```text
      f ∘ i       g
  A' ------> S <------ B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  left-concat-cospan-diagram :
    (𝒮 : cospan-diagram l1 l2 l3) {A' : UU l4} →
    (A' → domain-cospan-diagram 𝒮) → cospan-diagram l4 l2 l3
  left-concat-cospan-diagram 𝒮 f = concat-cospan-diagram 𝒮 f id
```

### Concatenating cospan diagrams and maps on the right

Consider a [cospan diagram](foundation.cospan-diagrams.md) `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and a map `j : B' → B`. The
{{#concept "right concatenation" Disambiguation="cospan diagram" Agda=right-concat-cospan-diagram}}
of `𝒮` by `j` is the cospan diagram

```text
        f       g ∘ j
  A' ------> S <------ B'.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  right-concat-cospan-diagram :
    (𝒮 : cospan-diagram l1 l2 l3) {B' : UU l4} →
    (B' → codomain-cospan-diagram 𝒮) → cospan-diagram l1 l4 l3
  right-concat-cospan-diagram 𝒮 g = concat-cospan-diagram 𝒮 id g
```

### Concatenation of cospan diagrams and morphisms of arrows on the left

Consider a cospan diagram `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f`
as indicated in the diagram

```text
          f         g
     A ------> S <------ B.
     |         |
  h₀ |         | h₁
     ∨         ∨
     A' -----> S'
          f'
```

Then we obtain a cospan diagram `A' --> S' <-- B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : A' → S')
  (h : hom-arrow (left-map-cospan-diagram 𝒮) f')
  where

  domain-left-concat-hom-arrow-cospan-diagram : UU l5
  domain-left-concat-hom-arrow-cospan-diagram = A'

  codomain-left-concat-hom-arrow-cospan-diagram : UU l2
  codomain-left-concat-hom-arrow-cospan-diagram = codomain-cospan-diagram 𝒮

  cospan-left-concat-hom-arrow-cospan-diagram :
    cospan l4
      ( domain-left-concat-hom-arrow-cospan-diagram)
      ( codomain-left-concat-hom-arrow-cospan-diagram)
  cospan-left-concat-hom-arrow-cospan-diagram =
    left-concat-hom-arrow-cospan
      ( cospan-cospan-diagram 𝒮)
      ( f')
      ( h)

  left-concat-hom-arrow-cospan-diagram : cospan-diagram l5 l2 l4
  pr1 left-concat-hom-arrow-cospan-diagram =
    domain-left-concat-hom-arrow-cospan-diagram
  pr1 (pr2 left-concat-hom-arrow-cospan-diagram) =
    codomain-left-concat-hom-arrow-cospan-diagram
  pr2 (pr2 left-concat-hom-arrow-cospan-diagram) =
    cospan-left-concat-hom-arrow-cospan-diagram

  cospanning-type-left-concat-hom-arrow-cospan-diagram : UU l4
  cospanning-type-left-concat-hom-arrow-cospan-diagram =
    cospanning-type-cospan-diagram left-concat-hom-arrow-cospan-diagram

  left-map-left-concat-hom-arrow-cospan-diagram :
    domain-left-concat-hom-arrow-cospan-diagram →
    cospanning-type-left-concat-hom-arrow-cospan-diagram
  left-map-left-concat-hom-arrow-cospan-diagram =
    left-map-cospan-diagram left-concat-hom-arrow-cospan-diagram

  right-map-left-concat-hom-arrow-cospan-diagram :
    codomain-left-concat-hom-arrow-cospan-diagram →
    cospanning-type-left-concat-hom-arrow-cospan-diagram
  right-map-left-concat-hom-arrow-cospan-diagram =
    right-map-cospan-diagram left-concat-hom-arrow-cospan-diagram
```

### Concatenation of cospan diagrams and morphisms of arrows on the right

Consider a cospan diagram `𝒮` given by

```text
       f         g
  A ------> S <------ B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow g' g`
as indicated in the diagram

```text
       f         g
  A ------> S <------ B.
            |         |
         h₀ |         | h₁
            ∨         ∨
            S' <----- B'
                 g'
```

Then we obtain a cospan diagram `A --> S' <-- B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : B' → S')
  (h : hom-arrow (right-map-cospan-diagram 𝒮) g')
  where

  domain-right-concat-hom-arrow-cospan-diagram : UU l1
  domain-right-concat-hom-arrow-cospan-diagram = domain-cospan-diagram 𝒮

  codomain-right-concat-hom-arrow-cospan-diagram : UU l5
  codomain-right-concat-hom-arrow-cospan-diagram = B'

  cospan-right-concat-hom-arrow-cospan-diagram :
    cospan l4
      ( domain-right-concat-hom-arrow-cospan-diagram)
      ( codomain-right-concat-hom-arrow-cospan-diagram)
  cospan-right-concat-hom-arrow-cospan-diagram =
    right-concat-hom-arrow-cospan
      ( cospan-cospan-diagram 𝒮)
      ( g')
      ( h)

  right-concat-hom-arrow-cospan-diagram : cospan-diagram l1 l5 l4
  pr1 right-concat-hom-arrow-cospan-diagram =
    domain-right-concat-hom-arrow-cospan-diagram
  pr1 (pr2 right-concat-hom-arrow-cospan-diagram) =
    codomain-right-concat-hom-arrow-cospan-diagram
  pr2 (pr2 right-concat-hom-arrow-cospan-diagram) =
    cospan-right-concat-hom-arrow-cospan-diagram

  cospanning-type-right-concat-hom-arrow-cospan-diagram : UU l4
  cospanning-type-right-concat-hom-arrow-cospan-diagram =
    cospanning-type-cospan-diagram right-concat-hom-arrow-cospan-diagram

  left-map-right-concat-hom-arrow-cospan-diagram :
    domain-right-concat-hom-arrow-cospan-diagram →
    cospanning-type-right-concat-hom-arrow-cospan-diagram
  left-map-right-concat-hom-arrow-cospan-diagram =
    left-map-cospan-diagram right-concat-hom-arrow-cospan-diagram

  right-map-right-concat-hom-arrow-cospan-diagram :
    codomain-right-concat-hom-arrow-cospan-diagram →
    cospanning-type-right-concat-hom-arrow-cospan-diagram
  right-map-right-concat-hom-arrow-cospan-diagram =
    right-map-cospan-diagram right-concat-hom-arrow-cospan-diagram
```
