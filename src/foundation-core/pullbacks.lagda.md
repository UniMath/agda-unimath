# Pullbacks

```agda
module foundation-core.pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.standard-pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

Consider a [cone](foundation.cones-over-cospan-diagrams.md) over a
[cospan diagram of types](foundation.cospan-diagrams.md) `f : A -> X <- B : g,`

```text
  C ------> B
  |         |
  |         | g
  ∨         ∨
  A ------> X.
       f
```

we want to pose the question of whether this cone is a
{{#concept "pullback cone" Disambiguation="types" Agda=is-pullback}}. Although
this concept is captured by
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md),
this is a large proposition, which is not suitable for all purposes. Therefore,
as our main definition of a pullback cone we consider the
{{#concept "small predicate of being a pullback" Agda=is-pullback}}: given the
existence of the [standard pullback type](foundation-core.standard-pullbacks.md)
`A ×_X B`, a cone is a _pullback_ if the gap map into the standard pullback is
an [equivalence](foundation-core.equivalences.md).

## Definitions

### The small property of being a pullback

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = is-equiv (gap f g c)
```

### A cone is a pullback if and only if it satisfies the universal property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) → universal-property-pullback f g c → is-pullback f g c
    is-pullback-universal-property-pullback c =
      is-equiv-up-pullback-up-pullback
        ( cone-standard-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-standard-pullback f g c)
        ( universal-property-standard-pullback f g)

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback f g c →
      universal-property-pullback f g c
    universal-property-pullback-is-pullback c is-pullback-c =
      up-pullback-up-pullback-is-equiv
        ( cone-standard-pullback f g)
        ( c)
        ( gap f g c)
        ( htpy-cone-up-pullback-standard-pullback f g c)
        ( is-pullback-c)
        ( universal-property-standard-pullback f g)
```

### The gap map into a pullback

The
{{#concept "gap map" Disambiguation="cone over a cospan" Agda=gap-is-pullback}}
of a [commuting square](foundation-core.commuting-squares-of-maps.md) is the map
from the domain of the cone into the pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) (H : is-pullback f g c)
  where

  gap-is-pullback : {l5 : Level} {C' : UU l5} → cone f g C' → C' → C
  gap-is-pullback =
    map-universal-property-pullback f g c
      ( universal-property-pullback-is-pullback f g c H)

  compute-gap-is-pullback :
    {l5 : Level} {C' : UU l5} (c' : cone f g C') →
    cone-map f g c (gap-is-pullback c') ＝ c'
  compute-gap-is-pullback =
    compute-map-universal-property-pullback f g c
      ( universal-property-pullback-is-pullback f g c H)
```

## Properties

### Pullbacks are symmetric

The pullback of `f : A → X ← B : g` is also the pullback of `g : B → X ← A : f`.

```agda
abstract
  is-pullback-swap-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (swap-cone f g c)
  is-pullback-swap-cone f g c is-pb-c =
    is-equiv-left-map-triangle
      ( gap g f (swap-cone f g c))
      ( map-commutative-standard-pullback f g)
      ( gap f g c)
      ( triangle-map-commutative-standard-pullback f g c)
      ( is-pb-c)
      ( is-equiv-map-commutative-standard-pullback f g)

abstract
  is-pullback-swap-cone' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback g f (swap-cone f g c) → is-pullback f g c
  is-pullback-swap-cone' f g c =
    is-equiv-top-map-triangle
      ( gap g f (swap-cone f g c))
      ( map-commutative-standard-pullback f g)
      ( gap f g c)
      ( triangle-map-commutative-standard-pullback f g c)
      ( is-equiv-map-commutative-standard-pullback f g)
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the vertical maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-map-fiber-vertical-map-cone :
    gap f g c ∘ map-equiv-total-fiber (pr1 c) ~
    tot (λ _ → tot (λ _ → inv)) ∘ tot (map-fiber-vertical-map-cone f g c)
  square-tot-map-fiber-vertical-map-cone
    (.(vertical-map-cone f g c x) , x , refl) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( inv (ap inv right-unit ∙ inv-inv (coherence-square-cone f g c x))))

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback :
      is-pullback f g c → is-fiberwise-equiv (map-fiber-vertical-map-cone f g c)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback pb =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fiber (vertical-map-cone f g c))
          ( tot (λ _ → tot (λ _ → inv)))
          ( tot (map-fiber-vertical-map-cone f g c))
          ( gap f g c)
          ( square-tot-map-fiber-vertical-map-cone)
          ( is-equiv-map-equiv-total-fiber (vertical-map-cone f g c))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ x →
              is-equiv-tot-is-fiberwise-equiv (λ y → is-equiv-inv (g y) (f x))))
          ( pb))

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone :
      is-fiberwise-equiv (map-fiber-vertical-map-cone f g c) → is-pullback f g c
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone is-equiv-fsq =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fiber (vertical-map-cone f g c))
        ( tot (λ _ → tot (λ _ → inv)))
        ( tot (map-fiber-vertical-map-cone f g c))
        ( gap f g c)
        ( square-tot-map-fiber-vertical-map-cone)
        ( is-equiv-map-equiv-total-fiber (vertical-map-cone f g c))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x →
            is-equiv-tot-is-fiberwise-equiv (λ y → is-equiv-inv (g y) (f x))))
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)
```

### The horizontal pullback pasting property

Given a diagram as follows where the right-hand square is a pullback

```text
  ∙ -------> ∙ -------> ∙
  |          | ⌟        |
  |          |          |
  v          v          v
  ∙ -------> ∙ -------> ∙,
```

then the left-hand square is a pullback if and only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c → is-pullback i (vertical-map-cone j h c) d →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d)
    is-pullback-rectangle-is-pullback-left-square c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone (j ∘ i) h
        ( pasting-horizontal-cone i j h c d)
        ( λ x →
          is-equiv-left-map-triangle
            ( map-fiber-vertical-map-cone
              ( j ∘ i) h (pasting-horizontal-cone i j h c d) x)
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
              ( i)
              ( vertical-map-cone j h c)
              ( d)
              ( is-pb-d)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j)
              ( h)
              ( c)
              ( is-pb-c)
              ( i x)))

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      (c : cone j h B) (d : cone i (vertical-map-cone j h c) A) →
      is-pullback j h c →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h c d) →
      is-pullback i (vertical-map-cone j h c) d
    is-pullback-left-square-is-pullback-rectangle c d is-pb-c is-pb-rect =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone i
        ( vertical-map-cone j h c)
        ( d)
        ( λ x →
          is-equiv-top-map-triangle
            ( map-fiber-vertical-map-cone
              ( j ∘ i) h (pasting-horizontal-cone i j h c d) x)
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
              ( j)
              ( h)
              ( c)
              ( is-pb-c)
              ( i x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j ∘ i)
              ( h)
              ( pasting-horizontal-cone i j h c d)
              ( is-pb-rect)
              ( x)))
```

### The vertical pullback pasting property

Given a diagram as follows where the lower square is a pullback

```text
  ∙ -------> ∙
  |          |
  |          |
  v          v
  ∙ -------> ∙
  | ⌟        |
  |          |
  v          v
  ∙ -------> ∙,
```

then the upper square is a pullback if and only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  abstract
    is-pullback-top-is-pullback-rectangle :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d) →
      is-pullback (horizontal-map-cone f g c) h d
    is-pullback-top-is-pullback-rectangle c d is-pb-c is-pb-dc =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( horizontal-map-cone f g c)
        ( h)
        ( d)
        ( λ x →
          is-fiberwise-equiv-is-equiv-map-Σ
            ( λ t → fiber h (pr1 t))
            ( map-fiber-vertical-map-cone f g c (vertical-map-cone f g c x))
            ( λ t →
              map-fiber-vertical-map-cone
                ( horizontal-map-cone f g c)
                ( h)
                ( d)
                ( pr1 t))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( f)
              ( g)
              ( c)
              ( is-pb-c)
              ( vertical-map-cone f g c x))
            ( is-equiv-top-is-equiv-bottom-square
              ( map-inv-compute-fiber-comp
                ( vertical-map-cone f g c)
                ( vertical-map-cone (horizontal-map-cone f g c) h d)
                ( vertical-map-cone f g c x))
              ( map-inv-compute-fiber-comp g h (f (vertical-map-cone f g c x)))
              ( map-Σ
                ( λ t → fiber h (pr1 t))
                ( map-fiber-vertical-map-cone f g c (vertical-map-cone f g c x))
                ( λ t →
                  map-fiber-vertical-map-cone
                    ( horizontal-map-cone f g c) h d (pr1 t)))
              ( map-fiber-vertical-map-cone f
                ( g ∘ h)
                ( pasting-vertical-cone f g h c d)
                ( vertical-map-cone f g c x))
              ( preserves-pasting-vertical-map-fiber-vertical-map-cone f g h c d
                ( vertical-map-cone f g c x))
              ( is-equiv-map-inv-compute-fiber-comp
                ( vertical-map-cone f g c)
                ( vertical-map-cone (horizontal-map-cone f g c) h d)
                ( vertical-map-cone f g c x))
              ( is-equiv-map-inv-compute-fiber-comp g h
                ( f (vertical-map-cone f g c x)))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f
                ( g ∘ h)
                ( pasting-vertical-cone f g h c d)
                ( is-pb-dc)
                ( vertical-map-cone f g c x)))
            ( x , refl))

  abstract
    is-pullback-rectangle-is-pullback-top :
      (c : cone f g B) (d : cone (horizontal-map-cone f g c) h A) →
      is-pullback f g c →
      is-pullback (horizontal-map-cone f g c) h d →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h c d)
    is-pullback-rectangle-is-pullback-top c d is-pb-c is-pb-d =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( f)
        ( g ∘ h)
        ( pasting-vertical-cone f g h c d)
        ( λ x →
          is-equiv-bottom-is-equiv-top-square
            ( map-inv-compute-fiber-comp
              ( vertical-map-cone f g c)
              ( vertical-map-cone (horizontal-map-cone f g c) h d)
              ( x))
            ( map-inv-compute-fiber-comp g h (f x))
            ( map-Σ
              ( λ t → fiber h (pr1 t))
              ( map-fiber-vertical-map-cone f g c x)
              ( λ t →
                map-fiber-vertical-map-cone
                  ( horizontal-map-cone f g c)
                  ( h)
                  ( d)
                  ( pr1 t)))
            ( map-fiber-vertical-map-cone
              ( f)
              ( g ∘ h)
              ( pasting-vertical-cone f g h c d)
              ( x))
            ( preserves-pasting-vertical-map-fiber-vertical-map-cone
              ( f)
              ( g)
              ( h)
              ( c)
              ( d)
              ( x))
            ( is-equiv-map-inv-compute-fiber-comp
              ( vertical-map-cone f g c)
              ( vertical-map-cone (horizontal-map-cone f g c) h d)
              ( x))
            ( is-equiv-map-inv-compute-fiber-comp g h (f x))
            ( is-equiv-map-Σ
              ( λ t → fiber h (pr1 t))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
                ( f)
                ( g)
                ( c)
                ( is-pb-c)
                ( x))
              ( λ t →
                is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
                  ( horizontal-map-cone f g c)
                  ( h)
                  ( d)
                  ( is-pb-d)
                  ( pr1 t))))
```

### Pullbacks can be "folded"

Given a pullback square

```text
         f'
    C -------> B
    | ⌟        |
  g'|          | g
    v          v
    A -------> X
         f
```

we can "fold" the vertical edge onto the horizontal one and get a new pullback
square

```text
            C ---------> X
            | ⌟          |
  (f' , g') |            |
            v            v
          A × B -----> X × X,
                f × g
```

moreover, this folded square is a pullback if and only if the original one is.

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  abstract
    is-pullback-fold-cone-is-pullback :
      {l4 : Level} {C : UU l4} (c : cone f g C) →
      is-pullback f g c →
      is-pullback (map-product f g) (diagonal X) (fold-cone f g c)
    is-pullback-fold-cone-is-pullback c is-pb-c =
      is-equiv-left-map-triangle
        ( gap (map-product f g) (diagonal X) (fold-cone f g c))
        ( map-fold-cone-standard-pullback f g)
        ( gap f g c)
        ( triangle-map-fold-cone-standard-pullback f g c)
        ( is-pb-c)
        ( is-equiv-map-fold-cone-standard-pullback f g)

  abstract
    is-pullback-is-pullback-fold-cone :
      {l4 : Level} {C : UU l4} (c : cone f g C) →
      is-pullback (map-product f g) (diagonal X) (fold-cone f g c) →
      is-pullback f g c
    is-pullback-is-pullback-fold-cone c =
      is-equiv-top-map-triangle
        ( gap (map-product f g) (diagonal X) (fold-cone f g c))
        ( map-fold-cone-standard-pullback f g)
        ( gap f g c)
        ( triangle-map-fold-cone-standard-pullback f g c)
        ( is-equiv-map-fold-cone-standard-pullback f g)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
