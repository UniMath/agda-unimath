# Descent for surjections

```agda
module foundation.descent-surjections where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.functoriality-fibers-of-maps
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.pullbacks
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="of surjections" Agda=iff-descent-surjection}}
of [surjections](foundation.surjective-maps.md) asserts that in a commuting
diagram of the form

```text
        p         q
   A ----->> B ------> C
   | ⌟       |         |
  f|        g|         |h
   ∨         ∨         ∨
   X ----->> Y ------> Z,
        i         j
```

where the maps `i` and `p` are surjective and the left hand square is a
pullback, then the right square is a [pullback](foundation-core.pullbacks.md) if
and only if the outer rectangle is a pullback.

This descent property appears as Theorem 2.3 in {{#cite CR21}}.

## Theorem

In the formalization we don't presuppose that `p` is surjective, as this follows
by base change stability of surjections.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  descent-is-surjective :
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
    is-surjective i →
    is-pullback i (vertical-map-cone j h c) d →
    is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) →
    is-pullback j h c
  descent-is-surjective i j h c d
    is-surjective-i is-pb-d is-pb-rectangle =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone j h c
      ( map-inv-is-equiv-precomp-Π-Prop-is-surjective
        ( is-surjective-i)
        ( λ y → is-equiv-Prop (map-fiber-vertical-map-cone j h c y))
        ( λ x →
          is-equiv-right-map-triangle
            ( map-fiber-vertical-map-cone (j ∘ i) h
              ( pasting-horizontal-cone i j h c d)
              ( x))
            ( map-fiber-vertical-map-cone j h c (i x))
            ( map-fiber-vertical-map-cone i (vertical-map-cone j h c) d x)
            ( preserves-pasting-horizontal-map-fiber-vertical-map-cone
                i j h c d x)
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j ∘ i)
              ( h)
              ( pasting-horizontal-cone i j h c d)
              ( is-pb-rectangle)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback i
              ( vertical-map-cone j h c)
              ( d)
              ( is-pb-d)
              ( x))))

  descent-surjection :
    (i : X ↠ Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone (map-surjection i) (vertical-map-cone j h c) A) →
    is-pullback (map-surjection i) (vertical-map-cone j h c) d →
    is-pullback
      ( j ∘ map-surjection i)
      ( h)
      ( pasting-horizontal-cone (map-surjection i) j h c d) →
    is-pullback j h c
  descent-surjection (i , I) j h c d =
    descent-is-surjective i j h c d I

  iff-descent-is-surjective :
    (i : X → Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
    is-surjective i →
    is-pullback i (vertical-map-cone j h c) d →
    is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) ↔
    is-pullback j h c
  iff-descent-is-surjective i j h c d is-surjective-i is-pb-d =
    ( descent-is-surjective i j h c d is-surjective-i is-pb-d ,
      ( λ C →
        is-pullback-rectangle-is-pullback-left-square i j h c d C is-pb-d))

  iff-descent-surjection :
    (i : X ↠ Y) (j : Y → Z) (h : C → Z)
    (c : cone j h B)
    (d : cone (map-surjection i) (vertical-map-cone j h c) A) →
    is-pullback (map-surjection i) (vertical-map-cone j h c) d →
    is-pullback
      ( j ∘ map-surjection i)
      ( h)
      ( pasting-horizontal-cone (map-surjection i) j h c d) ↔
    is-pullback j h c
  iff-descent-surjection (i , I) j h c d =
    iff-descent-is-surjective i j h c d I
```

## References

{{#bibliography}}

## Table of descent properties

{{#include tables/descent-properties.md}}
