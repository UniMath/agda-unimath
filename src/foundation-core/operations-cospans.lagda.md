# Operations on cospans

```agda
module foundation-core.operations-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains some operations on [cospans](foundation.cospans.md) that
produce new cospans from given cospans and possibly other data.

## Definitions

### Concatenating cospans and maps on both sides

Consider a [cospan](foundation.cospans.md) `s` given by

```text
       f         g
  A ------> S <------ B
```

and maps `i : A' → A` and `j : B' → B`. The
{{#concept "concatenation cospan" Disambiguation="cospan" Agda=concat-cospan}}
of `i`, `s`, and `j` is the cospan

```text
      f ∘ i     g ∘ j
  A' ------> S <------ B.
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3} {B' : UU l4}
  where

  concat-cospan : cospan l5 A B → (A' → A) → (B' → B) → cospan l5 A' B'
  pr1 (concat-cospan s i j) = cospanning-type-cospan s
  pr1 (pr2 (concat-cospan s i j)) = left-map-cospan s ∘ i
  pr2 (pr2 (concat-cospan s i j)) = right-map-cospan s ∘ j
```

### Concatenating cospans and maps on the left

Consider a [cospan](foundation.cospans.md) `s` given by

```text
       f         g
  A ------> S <------ B
```

and a map `i : A' → A`. The
{{#concept "left concatenation" Disambiguation="cospan" Agda=left-concat-cospan}}
of `s` by `i` is the cospan

```text
      f ∘ i       g
  A' ------> S <------ B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3}
  where

  left-concat-cospan : cospan l4 A B → (A' → A) → cospan l4 A' B
  left-concat-cospan s f = concat-cospan s f id
```

### Concatenating cospans and maps on the right

Consider a [cospan](foundation.cospans.md) `s` given by

```text
       f         g
  A ------> S <------ B
```

and a map `j : B' → B`. The
{{#concept "right concatenation" Disambiguation="cospan" Agda=right-concat-cospan}}
of `s` by `j` is the cospan

```text
        f       g ∘ j
  A' ------> S <------ B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {B' : UU l3}
  where

  right-concat-cospan : cospan l4 A B → (B' → B) → cospan l4 A B'
  right-concat-cospan s g = concat-cospan s id g
```

### Concatenating cospans and morphisms of arrows on the left

Consider a cospan `s` given by

```text
       f         g
  A ------> S <------ B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f f'`
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

Then we obtain a cospan `A' --> S' <-- B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} (s : cospan l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : A' → S')
  (h : hom-arrow (left-map-cospan s) f')
  where

  cospanning-type-left-concat-hom-arrow-cospan : UU l4
  cospanning-type-left-concat-hom-arrow-cospan = S'

  left-map-left-concat-hom-arrow-cospan :
    A' → cospanning-type-left-concat-hom-arrow-cospan
  left-map-left-concat-hom-arrow-cospan = f'

  right-map-left-concat-hom-arrow-cospan :
    B → cospanning-type-left-concat-hom-arrow-cospan
  right-map-left-concat-hom-arrow-cospan =
    map-codomain-hom-arrow (left-map-cospan s) f' h ∘ right-map-cospan s

  left-concat-hom-arrow-cospan : cospan l4 A' B
  pr1 left-concat-hom-arrow-cospan =
    cospanning-type-left-concat-hom-arrow-cospan
  pr1 (pr2 left-concat-hom-arrow-cospan) =
    left-map-left-concat-hom-arrow-cospan
  pr2 (pr2 left-concat-hom-arrow-cospan) =
    right-map-left-concat-hom-arrow-cospan
```

### Concatenating cospans and morphisms of arrows on the right

Consider a cospan `s` given by

```text
       f         g
  A ------> S <------ B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow g' g`
as indicated in the diagram

```text
       f         g
  A ------> S <------ B
            |         |
         h₀ |         | h₁
            ∨         ∨
            S' -----> B'.
                 g'
```

Then we obtain a cospan `A --> S' <-- B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2}
  (s : cospan l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : B' → S')
  (h : hom-arrow (right-map-cospan s) g')
  where

  cospanning-type-right-concat-hom-arrow-cospan : UU l4
  cospanning-type-right-concat-hom-arrow-cospan = S'

  left-map-right-concat-hom-arrow-cospan :
    A → cospanning-type-right-concat-hom-arrow-cospan
  left-map-right-concat-hom-arrow-cospan =
    map-codomain-hom-arrow (right-map-cospan s) g' h ∘ left-map-cospan s

  right-map-right-concat-hom-arrow-cospan :
    B' → cospanning-type-right-concat-hom-arrow-cospan
  right-map-right-concat-hom-arrow-cospan = g'

  right-concat-hom-arrow-cospan : cospan l4 A B'
  pr1 right-concat-hom-arrow-cospan =
    cospanning-type-right-concat-hom-arrow-cospan
  pr1 (pr2 right-concat-hom-arrow-cospan) =
    left-map-right-concat-hom-arrow-cospan
  pr2 (pr2 right-concat-hom-arrow-cospan) =
    right-map-right-concat-hom-arrow-cospan
```
