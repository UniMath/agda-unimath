# Descent for equivalences

```agda
module foundation.descent-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.functoriality-fibers-of-maps
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.pullbacks
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="of equivalences" Agda=iff-descent-equiv}}
of [equivalences](foundation-core.equivalences.md) is a somewhat degenerate form
of a descent property. It asserts that in a commuting diagram of the form

```text
        p         q
   A ------> B ------> C
   |         |         |
  f|        g|         |h
   ∨         ∨         ∨
   X ------> Y ------> Z,
        i         j
```

if the maps `i` and `p` are equivalences, then the right square is a
[pullback](foundation-core.pullbacks.md) if and only if the outer rectangle is a
pullback.

## Theorem

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  descent-is-equiv :
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone i (vertical-map-cone j h c) A) →
    is-equiv i →
    is-equiv (horizontal-map-cone i (vertical-map-cone j h c) d) →
    is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) →
    is-pullback j h c
  descent-is-equiv i j h c d
    is-equiv-i is-equiv-k is-pb-rectangle =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone j h c
      ( map-inv-is-equiv-precomp-Π-is-equiv
        ( is-equiv-i)
        ( λ y → is-equiv (map-fiber-vertical-map-cone j h c y))
        ( λ x →
          is-equiv-right-map-triangle
            ( map-fiber-vertical-map-cone (j ∘ i) h
              ( pasting-horizontal-cone i j h c d)
              ( x))
            ( map-fiber-vertical-map-cone j h c (i x))
            ( map-fiber-vertical-map-cone i (vertical-map-cone j h c) d x)
            ( preserves-pasting-horizontal-map-fiber-vertical-map-cone
              ( i)
              ( j)
              ( h)
              ( c)
              ( d)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j ∘ i)
              ( h)
              ( pasting-horizontal-cone i j h c d)
              ( is-pb-rectangle)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( i)
              ( vertical-map-cone j h c)
              ( d)
              ( is-pullback-is-equiv-horizontal-maps
                ( i)
                ( vertical-map-cone j h c)
                ( d)
                ( is-equiv-i)
                ( is-equiv-k))
              ( x))))

  descent-equiv :
    (i : X ≃ Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone (map-equiv i) (vertical-map-cone j h c) A) →
    is-equiv (horizontal-map-cone (map-equiv i) (vertical-map-cone j h c) d) →
    is-pullback
      ( j ∘ map-equiv i)
      ( h)
      ( pasting-horizontal-cone (map-equiv i) j h c d) →
    is-pullback j h c
  descent-equiv i j h c d =
    descent-is-equiv (map-equiv i) j h c d (is-equiv-map-equiv i)

  iff-descent-is-equiv :
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone i (vertical-map-cone j h c) A) →
    is-equiv i →
    is-equiv (horizontal-map-cone i (vertical-map-cone j h c) d) →
    is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) ↔
    is-pullback j h c
  iff-descent-is-equiv i j h c d I P =
    ( descent-is-equiv i j h c d I P ,
      λ C →
      is-pullback-rectangle-is-pullback-left-square i j h c d
        ( C)
        ( is-pullback-is-equiv-horizontal-maps i (vertical-map-cone j h c) d
          ( I)
          ( P)))

  iff-descent-equiv :
    (i : X ≃ Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone (map-equiv i) (vertical-map-cone j h c) A) →
    is-equiv (horizontal-map-cone (map-equiv i) (vertical-map-cone j h c) d) →
    is-pullback
      ( j ∘ map-equiv i)
      ( h)
      ( pasting-horizontal-cone (map-equiv i) j h c d) ↔
    is-pullback j h c
  iff-descent-equiv (i , I) j h c d =
    iff-descent-is-equiv i j h c d I
```

## Table of descent properties

{{#include tables/descent-properties.md}}
