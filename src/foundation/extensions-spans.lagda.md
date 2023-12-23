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

</details

## Idea

Consider a [span](foundation.spans.md) `s` given by

```text
       f       g
  A <----- S -----> B
```

and maps `i : A → A'` and `j : B → B'`. The {{#concept "extension" Disambiguation="span"}} of `s` by `i` and `j` is the span

```text
       i ∘ f     j ∘ g
  A' <------- S -------> B.
```

## Definitions

### Extensions of spans with fixed domain and codomain by equivalences of arrows on the left

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation.equivalence-arrows.md) `h : equiv-arrow f' f` as indicated in the diagram

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
  (s : span-fixed-domain-codomain l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : equiv-arrow f' (left-map-span-fixed-domain-codomain s))
  where

  spanning-type-left-extend-equiv-arrow-span-fixed-domain-codomain : UU l4
  spanning-type-left-extend-equiv-arrow-span-fixed-domain-codomain = S'

  left-map-left-extend-equiv-arrow-span-fixed-domain-codomain :
    spanning-type-left-extend-equiv-arrow-span-fixed-domain-codomain → A'
  left-map-left-extend-equiv-arrow-span-fixed-domain-codomain = f'

  right-map-left-extend-equiv-arrow-span-fixed-domain-codomain :
    spanning-type-left-extend-equiv-arrow-span-fixed-domain-codomain → B
  right-map-left-extend-equiv-arrow-span-fixed-domain-codomain =
    ( right-map-span-fixed-domain-codomain s) ∘
    ( map-domain-equiv-arrow f' (left-map-span-fixed-domain-codomain s) h)

  left-extend-equiv-arrow-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A' B
  pr1 left-extend-equiv-arrow-span-fixed-domain-codomain =
    spanning-type-left-extend-equiv-arrow-span-fixed-domain-codomain
  pr1 (pr2 left-extend-equiv-arrow-span-fixed-domain-codomain) =
    left-map-left-extend-equiv-arrow-span-fixed-domain-codomain
  pr2 (pr2 left-extend-equiv-arrow-span-fixed-domain-codomain) =
    right-map-left-extend-equiv-arrow-span-fixed-domain-codomain
```

### Extensions of spans with fixed domain and codomain by equivalences of arrows on the right

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow g' g` as indicated in the diagram

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
  (s : span-fixed-domain-codomain l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : equiv-arrow g' (right-map-span-fixed-domain-codomain s))
  where

  spanning-type-right-extend-equiv-arrow-span-fixed-domain-codomain : UU l4
  spanning-type-right-extend-equiv-arrow-span-fixed-domain-codomain = S'

  left-map-right-extend-equiv-arrow-span-fixed-domain-codomain :
    spanning-type-right-extend-equiv-arrow-span-fixed-domain-codomain → A
  left-map-right-extend-equiv-arrow-span-fixed-domain-codomain =
    ( left-map-span-fixed-domain-codomain s) ∘
    ( map-domain-equiv-arrow g' (right-map-span-fixed-domain-codomain s) h)

  right-map-right-extend-equiv-arrow-span-fixed-domain-codomain :
    spanning-type-right-extend-equiv-arrow-span-fixed-domain-codomain → B'
  right-map-right-extend-equiv-arrow-span-fixed-domain-codomain = g'

  right-extend-equiv-arrow-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B'
  pr1 right-extend-equiv-arrow-span-fixed-domain-codomain =
    spanning-type-right-extend-equiv-arrow-span-fixed-domain-codomain
  pr1 (pr2 right-extend-equiv-arrow-span-fixed-domain-codomain) =
    left-map-right-extend-equiv-arrow-span-fixed-domain-codomain
  pr2 (pr2 right-extend-equiv-arrow-span-fixed-domain-codomain) =
    right-map-right-extend-equiv-arrow-span-fixed-domain-codomain
```

#### Extensions of spans by equivalences of arrows on the left

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and an [equivalence of arrows](foundation.equivalence-arrows.md) `h : equiv-arrow f' f` as indicated in the diagram

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
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') (h : equiv-arrow f' (left-map-span s))
  where

  domain-left-extend-equiv-arrow-span : UU l5
  domain-left-extend-equiv-arrow-span = A'

  codomain-left-extend-equiv-arrow-span : UU l2
  codomain-left-extend-equiv-arrow-span = codomain-span s

  span-fixed-domain-codomain-left-extend-equiv-arrow-span :
    span-fixed-domain-codomain l4
      ( domain-left-extend-equiv-arrow-span)
      ( codomain-left-extend-equiv-arrow-span)
  span-fixed-domain-codomain-left-extend-equiv-arrow-span =
    left-extend-equiv-arrow-span-fixed-domain-codomain
      ( span-fixed-domain-codomain-span s)
      ( f')
      ( h)

  left-extend-equiv-arrow-span : span l5 l2 l4
  pr1 left-extend-equiv-arrow-span =
    domain-left-extend-equiv-arrow-span
  pr1 (pr2 left-extend-equiv-arrow-span) =
    codomain-left-extend-equiv-arrow-span
  pr2 (pr2 left-extend-equiv-arrow-span) =
    span-fixed-domain-codomain-left-extend-equiv-arrow-span

  spanning-type-left-extend-equiv-arrow-span : UU l4
  spanning-type-left-extend-equiv-arrow-span =
    spanning-type-span left-extend-equiv-arrow-span

  left-map-left-extend-equiv-arrow-span :
    spanning-type-left-extend-equiv-arrow-span →
    domain-left-extend-equiv-arrow-span
  left-map-left-extend-equiv-arrow-span =
    left-map-span left-extend-equiv-arrow-span

  right-map-left-extend-equiv-arrow-span :
    spanning-type-left-extend-equiv-arrow-span →
    codomain-left-extend-equiv-arrow-span
  right-map-left-extend-equiv-arrow-span =
    right-map-span left-extend-equiv-arrow-span
```

#### Extensions of spans by equivalences of arrows on the left

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and a [equivalence of arrows](foundation.equivalences-arrows.md) `h : equiv-arrow g' g` as indicated in the diagram

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
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : equiv-arrow g' (right-map-span s))
  where

  domain-right-extend-equiv-arrow-span : UU l1
  domain-right-extend-equiv-arrow-span = domain-span s

  codomain-right-extend-equiv-arrow-span : UU l5
  codomain-right-extend-equiv-arrow-span = B'

  span-fixed-domain-codomain-right-extend-equiv-arrow-span :
    span-fixed-domain-codomain l4
      ( domain-right-extend-equiv-arrow-span)
      ( codomain-right-extend-equiv-arrow-span)
  span-fixed-domain-codomain-right-extend-equiv-arrow-span =
    right-extend-equiv-arrow-span-fixed-domain-codomain
      ( span-fixed-domain-codomain-span s)
      ( g')
      ( h)

  right-extend-equiv-arrow-span : span l1 l5 l4
  pr1 right-extend-equiv-arrow-span =
    domain-right-extend-equiv-arrow-span
  pr1 (pr2 right-extend-equiv-arrow-span) =
    codomain-right-extend-equiv-arrow-span
  pr2 (pr2 right-extend-equiv-arrow-span) =
    span-fixed-domain-codomain-right-extend-equiv-arrow-span

  spanning-type-right-extend-equiv-arrow-span : UU l4
  spanning-type-right-extend-equiv-arrow-span =
    spanning-type-span right-extend-equiv-arrow-span

  left-map-right-extend-equiv-arrow-span :
    spanning-type-right-extend-equiv-arrow-span →
    domain-right-extend-equiv-arrow-span
  left-map-right-extend-equiv-arrow-span =
    left-map-span right-extend-equiv-arrow-span

  right-map-right-extend-equiv-arrow-span :
    spanning-type-right-extend-equiv-arrow-span →
    codomain-right-extend-equiv-arrow-span
  right-map-right-extend-equiv-arrow-span =
    right-map-span right-extend-equiv-arrow-span
```
