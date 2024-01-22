# Extensions of spans

```agda
module foundation-core.extensions-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "extension" Disambiguation="span"}} of `s` by `i` and `j` is the span

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B.
```

## Definitions

### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3} {B' : UU l4}
  where

  extend-span : span l5 A B → (A → A') → (B → B') → span l5 A' B'
  pr1 (extend-span s f g) = spanning-type-span s
  pr1 (pr2 (extend-span s f g)) = f ∘ left-map-span s
  pr2 (pr2 (extend-span s f g)) = g ∘ right-map-span s
```

### Extensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3}
  where

  left-extend-span : span l4 A B → (A → A') → span l4 A' B
  left-extend-span s f = extend-span s f id
```

### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1}
  {B : UU l3} {B' : UU l4}
  where

  right-extend-span : span l4 A B → (B → B') → span l4 A B'
  right-extend-span s g = extend-span s id g
```

### Extensions by morphisms of arrows on the left

Consider a span `s` given by

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

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} (s : span l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') (h : hom-arrow f' (left-map-span s))
  where

  spanning-type-left-extend-hom-arrow-span : UU l4
  spanning-type-left-extend-hom-arrow-span = S'

  left-map-left-extend-hom-arrow-span :
    spanning-type-left-extend-hom-arrow-span → A'
  left-map-left-extend-hom-arrow-span = f'

  right-map-left-extend-hom-arrow-span :
    spanning-type-left-extend-hom-arrow-span → B
  right-map-left-extend-hom-arrow-span =
    right-map-span s ∘ map-domain-hom-arrow f' (left-map-span s) h

  left-extend-hom-arrow-span : span l4 A' B
  pr1 left-extend-hom-arrow-span = spanning-type-left-extend-hom-arrow-span
  pr1 (pr2 left-extend-hom-arrow-span) = left-map-left-extend-hom-arrow-span
  pr2 (pr2 left-extend-hom-arrow-span) = right-map-left-extend-hom-arrow-span
```

### Extensions by morphisms of arrows on the right

Consider a span `s` given by

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

Then we obtain a span `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span s))
  where

  spanning-type-right-extend-hom-arrow-span : UU l4
  spanning-type-right-extend-hom-arrow-span = S'

  left-map-right-extend-hom-arrow-span :
    spanning-type-right-extend-hom-arrow-span → A
  left-map-right-extend-hom-arrow-span =
    left-map-span s ∘ map-domain-hom-arrow g' (right-map-span s) h

  right-map-right-extend-hom-arrow-span :
    spanning-type-right-extend-hom-arrow-span → B'
  right-map-right-extend-hom-arrow-span = g'

  right-extend-hom-arrow-span : span l4 A B'
  pr1 right-extend-hom-arrow-span = spanning-type-right-extend-hom-arrow-span
  pr1 (pr2 right-extend-hom-arrow-span) = left-map-right-extend-hom-arrow-span
  pr2 (pr2 right-extend-hom-arrow-span) = right-map-right-extend-hom-arrow-span
```
