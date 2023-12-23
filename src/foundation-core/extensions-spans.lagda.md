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

### Extensions of spans with fixed domain and codomain

#### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3} {B' : UU l4}
  where

  extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l5 A B → (A → A') → (B → B') →
    span-fixed-domain-codomain l5 A' B'
  pr1 (extend-span-fixed-domain-codomain s f g) =
    spanning-type-span-fixed-domain-codomain s
  pr1 (pr2 (extend-span-fixed-domain-codomain s f g)) =
    f ∘ left-map-span-fixed-domain-codomain s
  pr2 (pr2 (extend-span-fixed-domain-codomain s f g)) =
    g ∘ right-map-span-fixed-domain-codomain s
```

#### Extensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3}
  where

  left-extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B → (A → A') →
    span-fixed-domain-codomain l4 A' B
  left-extend-span-fixed-domain-codomain s f =
    extend-span-fixed-domain-codomain s f id
```

#### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1}
  {B : UU l3} {B' : UU l4}
  where

  right-extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B → (B → B') →
    span-fixed-domain-codomain l4 A B'
  right-extend-span-fixed-domain-codomain s g =
    extend-span-fixed-domain-codomain s id g
```

#### Extensions by morphisms of arrows on the left

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |
  f' |       f |
     V         V
     A' -----> A'.
          h₁
```

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (s : span-fixed-domain-codomain l3 A B)
  {S' : UU l4} {A' : UU l5} (f' : S' → A')
  (h : hom-arrow f' (left-map-span-fixed-domain-codomain s))
  where

  spanning-type-left-extend-hom-arrow-span-fixed-domain-codomain : UU l4
  spanning-type-left-extend-hom-arrow-span-fixed-domain-codomain = S'

  left-map-left-extend-hom-arrow-span-fixed-domain-codomain :
    spanning-type-left-extend-hom-arrow-span-fixed-domain-codomain → A'
  left-map-left-extend-hom-arrow-span-fixed-domain-codomain = f'

  right-map-left-extend-hom-arrow-span-fixed-domain-codomain :
    spanning-type-left-extend-hom-arrow-span-fixed-domain-codomain → B
  right-map-left-extend-hom-arrow-span-fixed-domain-codomain =
    ( right-map-span-fixed-domain-codomain s) ∘
    ( map-domain-hom-arrow f' (left-map-span-fixed-domain-codomain s) h)

  left-extend-hom-arrow-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A' B
  pr1 left-extend-hom-arrow-span-fixed-domain-codomain =
    spanning-type-left-extend-hom-arrow-span-fixed-domain-codomain
  pr1 (pr2 left-extend-hom-arrow-span-fixed-domain-codomain) =
    left-map-left-extend-hom-arrow-span-fixed-domain-codomain
  pr2 (pr2 left-extend-hom-arrow-span-fixed-domain-codomain) =
    right-map-left-extend-hom-arrow-span-fixed-domain-codomain
```

#### Extensions by morphisms of arrows on the right

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
  (s : span-fixed-domain-codomain l3 A B)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span-fixed-domain-codomain s))
  where

  spanning-type-right-extend-hom-arrow-span-fixed-domain-codomain : UU l4
  spanning-type-right-extend-hom-arrow-span-fixed-domain-codomain = S'

  left-map-right-extend-hom-arrow-span-fixed-domain-codomain :
    spanning-type-right-extend-hom-arrow-span-fixed-domain-codomain → A
  left-map-right-extend-hom-arrow-span-fixed-domain-codomain =
    ( left-map-span-fixed-domain-codomain s) ∘
    ( map-domain-hom-arrow g' (right-map-span-fixed-domain-codomain s) h)

  right-map-right-extend-hom-arrow-span-fixed-domain-codomain :
    spanning-type-right-extend-hom-arrow-span-fixed-domain-codomain → B'
  right-map-right-extend-hom-arrow-span-fixed-domain-codomain = g'

  right-extend-hom-arrow-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B'
  pr1 right-extend-hom-arrow-span-fixed-domain-codomain =
    spanning-type-right-extend-hom-arrow-span-fixed-domain-codomain
  pr1 (pr2 right-extend-hom-arrow-span-fixed-domain-codomain) =
    left-map-right-extend-hom-arrow-span-fixed-domain-codomain
  pr2 (pr2 right-extend-hom-arrow-span-fixed-domain-codomain) =
    right-map-right-extend-hom-arrow-span-fixed-domain-codomain
```

### Extensions of spans

#### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  where

  extend-span :
    (s : span l1 l2 l3)
    {A' : UU l4} (f : domain-span s → A')
    {B' : UU l5} (g : codomain-span s → B') →
    span l4 l5 l3
  pr1 (extend-span s {A'} f {B'} g) = A'
  pr1 (pr2 (extend-span s {A'} f {B'} g)) = B'
  pr2 (pr2 (extend-span s {A'} f {B'} g)) =
    extend-span-fixed-domain-codomain (span-fixed-domain-codomain-span s) f g
```

#### Extensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  left-extend-span :
    (s : span l1 l2 l3) {A' : UU l4} (f : domain-span s → A') → span l4 l2 l3
  left-extend-span s f = extend-span s f id
```

#### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  right-extend-span :
    (s : span l1 l2 l3) {B' : UU l4} (g : codomain-span s → B') → span l1 l4 l3
  right-extend-span s g = extend-span s id g
```

#### Extensions by morphisms of arrows on the left

Consider a `s` with fixed domain and codomain given by

```text
       f       g
  A <----- S -----> B
```

and a [morphism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |
  f' |       f |
     V         V
     A' -----> A'.
          h₁
```

Then we obtain a span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') (h : hom-arrow f' (left-map-span s))
  where

  domain-left-extend-hom-arrow-span : UU l5
  domain-left-extend-hom-arrow-span = A'

  codomain-left-extend-hom-arrow-span : UU l2
  codomain-left-extend-hom-arrow-span = codomain-span s

  span-fixed-domain-codomain-left-extend-hom-arrow-span :
    span-fixed-domain-codomain l4
      ( domain-left-extend-hom-arrow-span)
      ( codomain-left-extend-hom-arrow-span)
  span-fixed-domain-codomain-left-extend-hom-arrow-span =
    left-extend-hom-arrow-span-fixed-domain-codomain
      ( span-fixed-domain-codomain-span s)
      ( f')
      ( h)

  left-extend-hom-arrow-span : span l5 l2 l4
  pr1 left-extend-hom-arrow-span =
    domain-left-extend-hom-arrow-span
  pr1 (pr2 left-extend-hom-arrow-span) =
    codomain-left-extend-hom-arrow-span
  pr2 (pr2 left-extend-hom-arrow-span) =
    span-fixed-domain-codomain-left-extend-hom-arrow-span

  spanning-type-left-extend-hom-arrow-span : UU l4
  spanning-type-left-extend-hom-arrow-span =
    spanning-type-span left-extend-hom-arrow-span

  left-map-left-extend-hom-arrow-span :
    spanning-type-left-extend-hom-arrow-span →
    domain-left-extend-hom-arrow-span
  left-map-left-extend-hom-arrow-span =
    left-map-span left-extend-hom-arrow-span

  right-map-left-extend-hom-arrow-span :
    spanning-type-left-extend-hom-arrow-span →
    codomain-left-extend-hom-arrow-span
  right-map-left-extend-hom-arrow-span =
    right-map-span left-extend-hom-arrow-span
```

#### Extensions by morphisms of arrows on the left

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
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span s))
  where

  domain-right-extend-hom-arrow-span : UU l1
  domain-right-extend-hom-arrow-span = domain-span s

  codomain-right-extend-hom-arrow-span : UU l5
  codomain-right-extend-hom-arrow-span = B'

  span-fixed-domain-codomain-right-extend-hom-arrow-span :
    span-fixed-domain-codomain l4
      ( domain-right-extend-hom-arrow-span)
      ( codomain-right-extend-hom-arrow-span)
  span-fixed-domain-codomain-right-extend-hom-arrow-span =
    right-extend-hom-arrow-span-fixed-domain-codomain
      ( span-fixed-domain-codomain-span s)
      ( g')
      ( h)

  right-extend-hom-arrow-span : span l1 l5 l4
  pr1 right-extend-hom-arrow-span =
    domain-right-extend-hom-arrow-span
  pr1 (pr2 right-extend-hom-arrow-span) =
    codomain-right-extend-hom-arrow-span
  pr2 (pr2 right-extend-hom-arrow-span) =
    span-fixed-domain-codomain-right-extend-hom-arrow-span

  spanning-type-right-extend-hom-arrow-span : UU l4
  spanning-type-right-extend-hom-arrow-span =
    spanning-type-span right-extend-hom-arrow-span

  left-map-right-extend-hom-arrow-span :
    spanning-type-right-extend-hom-arrow-span →
    domain-right-extend-hom-arrow-span
  left-map-right-extend-hom-arrow-span =
    left-map-span right-extend-hom-arrow-span

  right-map-right-extend-hom-arrow-span :
    spanning-type-right-extend-hom-arrow-span →
    codomain-right-extend-hom-arrow-span
  right-map-right-extend-hom-arrow-span =
    right-map-span right-extend-hom-arrow-span
```
