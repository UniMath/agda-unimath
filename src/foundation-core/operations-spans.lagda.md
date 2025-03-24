# Operations on spans

```agda
open import foundation.function-extensionality-axiom

module foundation-core.operations-spans
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows funext
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains some operations on [spans](foundation.spans.md) that produce
new spans from given spans and possibly other data.

## Definitions

### Concatenating spans and maps on both sides

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The
{{#concept "concatenation span" Disambiguation="span" Agda=concat-span}} of `i`,
`s`, and `j` is the span

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B.
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3} {B' : UU l4}
  where

  concat-span : span l5 A B → (A → A') → (B → B') → span l5 A' B'
  pr1 (concat-span s i j) = spanning-type-span s
  pr1 (pr2 (concat-span s i j)) = i ∘ left-map-span s
  pr2 (pr2 (concat-span s i j)) = j ∘ right-map-span s
```

### Concatenating spans and maps on the left

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and a map `i : A → A'`. The
{{#concept "left concatenation" Disambiguation="span" Agda=left-concat-span}} of
`s` by `i` is the span

```text
       i ∘ f      g
  A' <------- S -----> B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3}
  where

  left-concat-span : span l4 A B → (A → A') → span l4 A' B
  left-concat-span s f = concat-span s f id
```

### Concatenating spans and maps on the right

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and a map `j : B → B'`. The
{{#concept "right concatenation" Disambiguation="span" Agda=right-concat-span}}
of `s` by `j` is the span

```text
        f      j ∘ g
  A' <----- S -------> B.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1}
  {B : UU l3} {B' : UU l4}
  where

  right-concat-span : span l4 A B → (B → B') → span l4 A B'
  right-concat-span s g = concat-span s id g
```

### Concatenating spans and morphisms of arrows on the left

Consider a span `s` given by

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

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} (s : span l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') (h : hom-arrow f' (left-map-span s))
  where

  spanning-type-left-concat-hom-arrow-span : UU l4
  spanning-type-left-concat-hom-arrow-span = S'

  left-map-left-concat-hom-arrow-span :
    spanning-type-left-concat-hom-arrow-span → A'
  left-map-left-concat-hom-arrow-span = f'

  right-map-left-concat-hom-arrow-span :
    spanning-type-left-concat-hom-arrow-span → B
  right-map-left-concat-hom-arrow-span =
    right-map-span s ∘ map-domain-hom-arrow f' (left-map-span s) h

  left-concat-hom-arrow-span : span l4 A' B
  pr1 left-concat-hom-arrow-span = spanning-type-left-concat-hom-arrow-span
  pr1 (pr2 left-concat-hom-arrow-span) = left-map-left-concat-hom-arrow-span
  pr2 (pr2 left-concat-hom-arrow-span) = right-map-left-concat-hom-arrow-span
```

### Concatenating spans and morphisms of arrows on the right

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
  (h : hom-arrow g' (right-map-span s))
  where

  spanning-type-right-concat-hom-arrow-span : UU l4
  spanning-type-right-concat-hom-arrow-span = S'

  left-map-right-concat-hom-arrow-span :
    spanning-type-right-concat-hom-arrow-span → A
  left-map-right-concat-hom-arrow-span =
    left-map-span s ∘ map-domain-hom-arrow g' (right-map-span s) h

  right-map-right-concat-hom-arrow-span :
    spanning-type-right-concat-hom-arrow-span → B'
  right-map-right-concat-hom-arrow-span = g'

  right-concat-hom-arrow-span : span l4 A B'
  pr1 right-concat-hom-arrow-span = spanning-type-right-concat-hom-arrow-span
  pr1 (pr2 right-concat-hom-arrow-span) = left-map-right-concat-hom-arrow-span
  pr2 (pr2 right-concat-hom-arrow-span) = right-map-right-concat-hom-arrow-span
```
