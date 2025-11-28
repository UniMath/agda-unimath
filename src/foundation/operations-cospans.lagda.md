# Operations on cospans

```agda
module foundation.operations-cospans where

open import foundation-core.operations-cospans public
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains some further operations on [cospans](foundation.cospans.md)
that produce new cospans from given cospans and possibly other data. Previous
operations on cospans were defined in
[`foundation-core.operations-cospans`](foundation-core.operations-cospans.md).

## Definitions

### Concatenating cospans and equivalences of arrows on the left

Consider a cospan `s` given by

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

Then we obtain a cospan `A' --> S' <-- B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : cospan l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : A' → S')
  (h : equiv-arrow (left-map-cospan s) f')
  where

  cospanning-type-left-concat-equiv-arrow-cospan : UU l4
  cospanning-type-left-concat-equiv-arrow-cospan = S'

  left-map-left-concat-equiv-arrow-cospan :
    A' → cospanning-type-left-concat-equiv-arrow-cospan
  left-map-left-concat-equiv-arrow-cospan = f'

  right-map-left-concat-equiv-arrow-cospan :
    B → cospanning-type-left-concat-equiv-arrow-cospan
  right-map-left-concat-equiv-arrow-cospan =
    map-codomain-equiv-arrow (left-map-cospan s) f' h ∘ right-map-cospan s

  left-concat-equiv-arrow-cospan :
    cospan l4 A' B
  pr1 left-concat-equiv-arrow-cospan =
    cospanning-type-left-concat-equiv-arrow-cospan
  pr1 (pr2 left-concat-equiv-arrow-cospan) =
    left-map-left-concat-equiv-arrow-cospan
  pr2 (pr2 left-concat-equiv-arrow-cospan) =
    right-map-left-concat-equiv-arrow-cospan
```

### Concatenating cospans and equivalences of arrows on the right

Consider a cospan `s` given by

```text
       f         g
  A ------> S <------ B
```

and an equivalence of arrows `h : equiv-arrow g' g` as indicated in the diagram

```text
       f         g
  A ------> S <------ B
            |         |
         h₀ | ≃     ≃ | h₁
            ∨         ∨
            S' <----- B'.
                 g'
```

Then we obtain a cospan `A --> S' <-- B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : cospan l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : B' → S')
  (h : equiv-arrow (right-map-cospan s) g')
  where

  cospanning-type-right-concat-equiv-arrow-cospan : UU l4
  cospanning-type-right-concat-equiv-arrow-cospan = S'

  left-map-right-concat-equiv-arrow-cospan :
    A → cospanning-type-right-concat-equiv-arrow-cospan
  left-map-right-concat-equiv-arrow-cospan =
    map-codomain-equiv-arrow (right-map-cospan s) g' h ∘ left-map-cospan s

  right-map-right-concat-equiv-arrow-cospan :
    B' → cospanning-type-right-concat-equiv-arrow-cospan
  right-map-right-concat-equiv-arrow-cospan = g'

  right-concat-equiv-arrow-cospan :
    cospan l4 A B'
  pr1 right-concat-equiv-arrow-cospan =
    cospanning-type-right-concat-equiv-arrow-cospan
  pr1 (pr2 right-concat-equiv-arrow-cospan) =
    left-map-right-concat-equiv-arrow-cospan
  pr2 (pr2 right-concat-equiv-arrow-cospan) =
    right-map-right-concat-equiv-arrow-cospan
```

## See also

- [Composition of cospans](foundation.composition-cospans.md)
- [Opposite cospans](foundation.opposite-cospans.md)
