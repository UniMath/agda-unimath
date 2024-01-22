# Extensions of spans

```agda
module foundation.extensions-spans where

open import foundation-core.extensions-spans public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
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

### Extensions of spans with fixed domain and codomain by equivalences of arrows on the left

Consider a span `s` given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation.equivalence-arrows.md)
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

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : equiv-arrow f' (left-map-span s))
  where

  spanning-type-left-extend-equiv-arrow-span : UU l4
  spanning-type-left-extend-equiv-arrow-span = S'

  left-map-left-extend-equiv-arrow-span :
    spanning-type-left-extend-equiv-arrow-span → A'
  left-map-left-extend-equiv-arrow-span = f'

  right-map-left-extend-equiv-arrow-span :
    spanning-type-left-extend-equiv-arrow-span → B
  right-map-left-extend-equiv-arrow-span =
    ( right-map-span s) ∘
    ( map-domain-equiv-arrow f' (left-map-span s) h)

  left-extend-equiv-arrow-span :
    span l4 A' B
  pr1 left-extend-equiv-arrow-span =
    spanning-type-left-extend-equiv-arrow-span
  pr1 (pr2 left-extend-equiv-arrow-span) =
    left-map-left-extend-equiv-arrow-span
  pr2 (pr2 left-extend-equiv-arrow-span) =
    right-map-left-extend-equiv-arrow-span
```

### Extensions of spans with fixed domain and codomain by equivalences of arrows on the right

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
  h₀ | ≃    ≃ | h₁
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
  (h : equiv-arrow g' (right-map-span s))
  where

  spanning-type-right-extend-equiv-arrow-span : UU l4
  spanning-type-right-extend-equiv-arrow-span = S'

  left-map-right-extend-equiv-arrow-span :
    spanning-type-right-extend-equiv-arrow-span → A
  left-map-right-extend-equiv-arrow-span =
    ( left-map-span s) ∘
    ( map-domain-equiv-arrow g' (right-map-span s) h)

  right-map-right-extend-equiv-arrow-span :
    spanning-type-right-extend-equiv-arrow-span → B'
  right-map-right-extend-equiv-arrow-span = g'

  right-extend-equiv-arrow-span :
    span l4 A B'
  pr1 right-extend-equiv-arrow-span =
    spanning-type-right-extend-equiv-arrow-span
  pr1 (pr2 right-extend-equiv-arrow-span) =
    left-map-right-extend-equiv-arrow-span
  pr2 (pr2 right-extend-equiv-arrow-span) =
    right-map-right-extend-equiv-arrow-span
```
