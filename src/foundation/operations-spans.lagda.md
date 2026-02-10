# Operations on spans

```agda
module foundation.operations-spans where

open import foundation-core.operations-spans public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.equivalences-arrows
open import foundation-core.function-types
```

</details>

## Idea

This file contains some further operations on [spans](foundation.spans.md) that
produce new spans from given spans and possibly other data. Previous operations
on spans were defined in
[`foundation-core.operations-spans`](foundation-core.operations-spans.md).

## Definitions

### Concatenating spans and equivalences of arrows on the left

Consider a span `s` given by

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

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : equiv-arrow f' (left-map-span s))
  where

  spanning-type-left-concat-equiv-arrow-span : UU l4
  spanning-type-left-concat-equiv-arrow-span = S'

  left-map-left-concat-equiv-arrow-span :
    spanning-type-left-concat-equiv-arrow-span → A'
  left-map-left-concat-equiv-arrow-span = f'

  right-map-left-concat-equiv-arrow-span :
    spanning-type-left-concat-equiv-arrow-span → B
  right-map-left-concat-equiv-arrow-span =
    ( right-map-span s) ∘
    ( map-domain-equiv-arrow f' (left-map-span s) h)

  left-concat-equiv-arrow-span :
    span l4 A' B
  pr1 left-concat-equiv-arrow-span =
    spanning-type-left-concat-equiv-arrow-span
  pr1 (pr2 left-concat-equiv-arrow-span) =
    left-map-left-concat-equiv-arrow-span
  pr2 (pr2 left-concat-equiv-arrow-span) =
    right-map-left-concat-equiv-arrow-span
```

### Concatenating spans and equivalences of arrows on the right

Consider a span `s` given by

```text
       f       g
  A <----- S -----> B
```

and a equivalence of arrows `h : equiv-arrow g' g` as indicated in the diagram

```text
               g'
           S' ----> B'
           |        |
        h₀ | ≃    ≃ | h₁
           ∨        ∨
  A <----- S -----> B.
       f       g
```

Then we obtain a span `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : equiv-arrow g' (right-map-span s))
  where

  spanning-type-right-concat-equiv-arrow-span : UU l4
  spanning-type-right-concat-equiv-arrow-span = S'

  left-map-right-concat-equiv-arrow-span :
    spanning-type-right-concat-equiv-arrow-span → A
  left-map-right-concat-equiv-arrow-span =
    ( left-map-span s) ∘
    ( map-domain-equiv-arrow g' (right-map-span s) h)

  right-map-right-concat-equiv-arrow-span :
    spanning-type-right-concat-equiv-arrow-span → B'
  right-map-right-concat-equiv-arrow-span = g'

  right-concat-equiv-arrow-span :
    span l4 A B'
  pr1 right-concat-equiv-arrow-span =
    spanning-type-right-concat-equiv-arrow-span
  pr1 (pr2 right-concat-equiv-arrow-span) =
    left-map-right-concat-equiv-arrow-span
  pr2 (pr2 right-concat-equiv-arrow-span) =
    right-map-right-concat-equiv-arrow-span
```

## See also

- [Composition of spans](foundation.composition-spans.md)
- [Opposite spans](foundation.opposite-spans.md)
