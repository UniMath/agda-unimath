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
open import foundation.morphisms-arrows
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-standard-pullbacks
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.diagonal-maps-cartesian-products-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
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
that is a large proposition, which is not suitable for all purposes. Therefore,
as our main definition of a pullback cone we consider the
{{#concept "small predicate of being a pullback" Agda=is-pullback}}: given the
existence of the [standard pullback type](foundation.standard-pullbacks.md)
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

### The homotopy of cones obtained from the universal property of pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  (c : cone f g C) (up : is-pullback f g c)
  {l5 : Level} {C' : UU l5} (c' : cone f g C')
  where

  htpy-cone-gap-is-pullback :
    htpy-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
  htpy-cone-gap-is-pullback =
    htpy-eq-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
      ( compute-gap-is-pullback f g c up c')

  htpy-vertical-map-gap-is-pullback :
    vertical-map-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c')) ~
      vertical-map-cone f g c'
  htpy-vertical-map-gap-is-pullback =
    htpy-vertical-map-htpy-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
      ( htpy-cone-gap-is-pullback)

  htpy-horizontal-map-gap-is-pullback :
    horizontal-map-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c')) ~
      horizontal-map-cone f g c'
  htpy-horizontal-map-gap-is-pullback =
    htpy-horizontal-map-htpy-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
      ( htpy-cone-gap-is-pullback)

  coh-htpy-cone-gap-is-pullback :
    coherence-htpy-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
      ( htpy-vertical-map-gap-is-pullback)
      ( htpy-horizontal-map-gap-is-pullback)
  coh-htpy-cone-gap-is-pullback =
    coh-htpy-cone f g
      ( cone-map f g c (gap-is-pullback f g c up c'))
      ( c')
      ( htpy-cone-gap-is-pullback)
```

## Properties

### The standard pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  is-pullback-standard-pullback : is-pullback f g (cone-standard-pullback f g)
  is-pullback-standard-pullback = is-equiv-id
```

### The identity cone is a pullback

```agda
is-pullback-id-cone : {l : Level} (A : UU l) → is-pullback id id (id-cone A)
is-pullback-id-cone A =
  is-equiv-is-invertible pr1 (λ where (x , .x , refl) → refl) refl-htpy
```

### Pullbacks are preserved under homotopies of parallel cones

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  triangle-is-pullback-htpy :
    {c : cone f g C} {c' : cone f' g' C} (Hc : htpy-parallel-cone Hf Hg c c') →
    gap f g c ~ map-equiv-standard-pullback-htpy Hf Hg ∘ gap f' g' c'
  triangle-is-pullback-htpy {p , q , H} {p' , q' , H'} (Hp , Hq , HH) z =
    eq-Eq-standard-pullback f g
      ( Hp z)
      ( Hq z)
      ( ( inv (assoc (ap f (Hp z)) (Hf (p' z) ∙ H' z) (inv (Hg (q' z))))) ∙
        ( inv
          ( right-transpose-eq-concat
            ( H z ∙ ap g (Hq z))
            ( Hg (q' z))
            ( ap f (Hp z) ∙ (Hf (p' z) ∙ H' z))
            ( ( assoc (H z) (ap g (Hq z)) (Hg (q' z))) ∙
              ( HH z) ∙
              ( assoc (ap f (Hp z)) (Hf (p' z)) (H' z))))))

  abstract
    is-pullback-htpy :
      {c : cone f g C} (c' : cone f' g' C) →
      htpy-parallel-cone Hf Hg c c' →
      is-pullback f' g' c' → is-pullback f g c
    is-pullback-htpy {c} c' H pb-c' =
      is-equiv-left-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( pb-c')
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)

  abstract
    is-pullback-htpy' :
      (c : cone f g C) {c' : cone f' g' C} →
      htpy-parallel-cone Hf Hg c c' →
      is-pullback f g c → is-pullback f' g' c'
    is-pullback-htpy' c {c'} H =
      is-equiv-top-map-triangle
        ( gap f g c)
        ( map-equiv-standard-pullback-htpy Hf Hg)
        ( gap f' g' c')
        ( triangle-is-pullback-htpy H)
        ( is-equiv-map-equiv-standard-pullback-htpy Hf Hg)
```

### Pullbacks are symmetric

The pullback of `f : A → X ← B : g` is also the pullback of `g : B → X ← A : f`.

```agda
abstract
  is-pullback-swap-cone :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-pullback g f (swap-cone f g c)
  is-pullback-swap-cone f g c pb-c =
    is-equiv-left-map-triangle
      ( gap g f (swap-cone f g c))
      ( map-commutative-standard-pullback f g)
      ( gap f g c)
      ( triangle-map-commutative-standard-pullback f g c)
      ( pb-c)
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

A cone is a pullback if and only if the induced family of maps on fibers between
the vertical maps is a family of equivalences

```text
  fiber i a --> fiber g (f a)
      |               |
      |               |
      ∨               ∨
      C ------------> B
      |               |
    i |               | g
      ∨               ∨
  a ∈ A ------------> X.
              f
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  triangle-tot-map-fiber-vertical-map-cone' :
    tot (map-fiber-vertical-map-cone' f g c) ~
    gap f g c ∘ map-equiv-total-fiber' (vertical-map-cone f g c)
  triangle-tot-map-fiber-vertical-map-cone'
    (.(vertical-map-cone f g c x) , x , refl) = refl

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' :
      is-pullback f g c →
      is-fiberwise-equiv (map-fiber-vertical-map-cone' f g c)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' pb =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-left-map-triangle
          ( tot (map-fiber-vertical-map-cone' f g c))
          ( gap f g c)
          ( map-equiv-total-fiber' (vertical-map-cone f g c))
          ( triangle-tot-map-fiber-vertical-map-cone')
          ( is-equiv-map-equiv-total-fiber' (vertical-map-cone f g c))
          ( pb))

  fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' :
      is-pullback f g c → (x : A) →
      fiber' (vertical-map-cone f g c) x ≃ fiber' g (f x)
  fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' pb x =
    ( map-fiber-vertical-map-cone' f g c x ,
      is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' pb x)

  equiv-tot-map-fiber-vertical-map-cone-is-pullback' :
      is-pullback f g c →
      Σ A (fiber' (vertical-map-cone f g c)) ≃ Σ A (fiber' g ∘ f)
  equiv-tot-map-fiber-vertical-map-cone-is-pullback' pb =
    equiv-tot (fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback' pb)

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone' :
      is-fiberwise-equiv (map-fiber-vertical-map-cone' f g c) →
      is-pullback f g c
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone' is-equiv-fsq =
      is-equiv-right-map-triangle
        ( tot (map-fiber-vertical-map-cone' f g c))
        ( gap f g c)
        ( map-equiv-total-fiber' (vertical-map-cone f g c))
        ( triangle-tot-map-fiber-vertical-map-cone')
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-fsq)
        ( is-equiv-map-equiv-total-fiber' (vertical-map-cone f g c))

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback' :
      universal-property-pullback f g c →
      is-fiberwise-equiv (map-fiber-vertical-map-cone' f g c)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
      up =
      is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback'
        ( is-pullback-universal-property-pullback f g c up)

  fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback' :
      universal-property-pullback f g c → (x : A) →
      fiber' (vertical-map-cone f g c) x ≃ fiber' g (f x)
  fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
    pb x =
    ( map-fiber-vertical-map-cone' f g c x ,
      is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
        ( pb)
        ( x))

  equiv-tot-map-fiber-vertical-map-cone-universal-property-pullback' :
      universal-property-pullback f g c →
      Σ A (fiber' (vertical-map-cone f g c)) ≃ Σ A (fiber' g ∘ f)
  equiv-tot-map-fiber-vertical-map-cone-universal-property-pullback' pb =
    equiv-tot
      ( fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback'
        ( pb))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-map-fiber-vertical-map-cone :
    gap f g c ∘ map-equiv-total-fiber (vertical-map-cone f g c) ~
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

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback :
      universal-property-pullback f g c →
      is-fiberwise-equiv (map-fiber-vertical-map-cone f g c)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-universal-property-pullback
      up =
      is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
        ( is-pullback-universal-property-pullback f g c up)
```

### A cone is a pullback if and only if it induces a family of equivalences between the fibers of the horizontal maps

A cone is a pullback if and only if the induced family of maps on fibers between
the horizontal maps is a family of equivalences

```text
                            j
      fiber j b ----> C --------> B ∋ b
          |           |           |
          |           |           | g
          ∨           ∨           ∨
    fiber f (g b) --> A --------> X.
                            f
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C)
  where

  square-tot-map-fiber-horizontal-map-cone :
    ( gap g f (swap-cone f g c) ∘
      map-equiv-total-fiber (horizontal-map-cone f g c)) ~
    ( tot (λ _ → tot (λ _ → inv)) ∘
      tot (map-fiber-horizontal-map-cone f g c))
  square-tot-map-fiber-horizontal-map-cone
    (.(horizontal-map-cone f g c x) , x , refl) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( ap
          ( inv)
          ( inv (right-unit ∙ inv-inv (coherence-square-cone f g c x)))))

  square-tot-map-fiber-horizontal-map-cone' :
    ( ( λ x →
        ( horizontal-map-cone f g c x ,
          vertical-map-cone f g c x ,
          coherence-square-cone f g c x)) ∘
      map-equiv-total-fiber (horizontal-map-cone f g c)) ~
    tot (map-fiber-horizontal-map-cone f g c)
  square-tot-map-fiber-horizontal-map-cone'
    (.(horizontal-map-cone f g c x) , x , refl) =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( inv (right-unit ∙ inv-inv (coherence-square-cone f g c x))))

  abstract
    is-fiberwise-equiv-map-fiber-horizontal-map-cone-is-pullback :
      is-pullback f g c →
      is-fiberwise-equiv (map-fiber-horizontal-map-cone f g c)
    is-fiberwise-equiv-map-fiber-horizontal-map-cone-is-pullback pb =
      is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback g f
        ( swap-cone f g c)
        ( is-pullback-swap-cone f g c pb)

  abstract
    is-pullback-is-fiberwise-equiv-map-fiber-horizontal-map-cone :
      is-fiberwise-equiv (map-fiber-horizontal-map-cone f g c) →
      is-pullback f g c
    is-pullback-is-fiberwise-equiv-map-fiber-horizontal-map-cone is-equiv-fsq =
      is-pullback-swap-cone' f g c
        ( is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone g f
          ( swap-cone f g c)
          ( is-equiv-fsq))
```

### The horizontal pullback pasting property

Given a diagram as follows where the right-hand square is a pullback

```text
  ∙ -------> ∙ -------> ∙
  |          | ⌟        |
  |          |          |
  ∨          ∨          ∨
  ∙ -------> ∙ -------> ∙,
```

then the left-hand square is a pullback if and only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  (right : cone j h B) (left : cone i (vertical-map-cone j h right) A)
  where

  abstract
    is-pullback-rectangle-is-pullback-left-square :
      is-pullback j h right → is-pullback i (vertical-map-cone j h right) left →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h right left)
    is-pullback-rectangle-is-pullback-left-square pb-c pb-d =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone (j ∘ i) h
        ( pasting-horizontal-cone i j h right left)
        ( λ x →
          is-equiv-left-map-triangle
            ( map-fiber-vertical-map-cone
              ( j ∘ i) h (pasting-horizontal-cone i j h right left) x)
            ( map-fiber-vertical-map-cone j h right (i x))
            ( map-fiber-vertical-map-cone
              ( i)
              ( vertical-map-cone j h right)
              ( left)
              ( x))
            ( preserves-pasting-horizontal-map-fiber-vertical-map-cone
              ( i)
              ( j)
              ( h)
              ( right)
              ( left)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( i)
              ( vertical-map-cone j h right)
              ( left)
              ( pb-d)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j)
              ( h)
              ( right)
              ( pb-c)
              ( i x)))

  abstract
    is-pullback-left-square-is-pullback-rectangle :
      is-pullback j h right →
      is-pullback (j ∘ i) h (pasting-horizontal-cone i j h right left) →
      is-pullback i (vertical-map-cone j h right) left
    is-pullback-left-square-is-pullback-rectangle pb-c pb-rect =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone i
        ( vertical-map-cone j h right)
        ( left)
        ( λ x →
          is-equiv-top-map-triangle
            ( map-fiber-vertical-map-cone
              ( j ∘ i) h (pasting-horizontal-cone i j h right left) x)
            ( map-fiber-vertical-map-cone j h right (i x))
            ( map-fiber-vertical-map-cone
              ( i)
              ( vertical-map-cone j h right)
              ( left)
              ( x))
            ( preserves-pasting-horizontal-map-fiber-vertical-map-cone
              ( i)
              ( j)
              ( h)
              ( right)
              ( left)
              ( x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j)
              ( h)
              ( right)
              ( pb-c)
              ( i x))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( j ∘ i)
              ( h)
              ( pasting-horizontal-cone i j h right left)
              ( pb-rect)
              ( x)))
```

### The vertical pullback pasting property

Given a diagram as follows where the lower square is a pullback

```text
  ∙ -------> ∙
  |          |
  |          |
  ∨          ∨
  ∙ -------> ∙
  | ⌟        |
  |          |
  ∨          ∨
  ∙ -------> ∙,
```

then the upper square is a pullback if and only if the composite square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  (lower : cone f g B)
  (upper : cone (horizontal-map-cone f g lower) h A)
  where

  abstract
    is-pullback-top-square-is-pullback-rectangle :
      is-pullback f g lower →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h lower upper) →
      is-pullback (horizontal-map-cone f g lower) h upper
    is-pullback-top-square-is-pullback-rectangle pb-lower pb-rect =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( horizontal-map-cone f g lower)
        ( h)
        ( upper)
        ( λ x →
          is-fiberwise-equiv-is-equiv-map-Σ
            ( λ t → fiber h (pr1 t))
            ( map-fiber-vertical-map-cone f g
              ( lower)
              ( vertical-map-cone f g lower x))
            ( λ t →
              map-fiber-vertical-map-cone
                ( horizontal-map-cone f g lower)
                ( h)
                ( upper)
                ( pr1 t))
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              ( f)
              ( g)
              ( lower)
              ( pb-lower)
              ( vertical-map-cone f g lower x))
            ( is-equiv-top-is-equiv-bottom-square
              ( map-inv-compute-fiber-comp
                ( vertical-map-cone f g lower)
                ( vertical-map-cone (horizontal-map-cone f g lower) h upper)
                ( vertical-map-cone f g lower x))
              ( map-inv-compute-fiber-comp g h
                ( f (vertical-map-cone f g lower x)))
              ( map-Σ
                ( λ t → fiber h (pr1 t))
                ( map-fiber-vertical-map-cone f g
                  ( lower)
                  ( vertical-map-cone f g lower x))
                ( λ t →
                  map-fiber-vertical-map-cone
                    ( horizontal-map-cone f g lower) h upper (pr1 t)))
              ( map-fiber-vertical-map-cone f
                ( g ∘ h)
                ( pasting-vertical-cone f g h lower upper)
                ( vertical-map-cone f g lower x))
              ( preserves-pasting-vertical-map-fiber-vertical-map-cone f g h
                ( lower)
                ( upper)
                ( vertical-map-cone f g lower x))
              ( is-equiv-map-inv-compute-fiber-comp
                ( vertical-map-cone f g lower)
                ( vertical-map-cone (horizontal-map-cone f g lower) h upper)
                ( vertical-map-cone f g lower x))
              ( is-equiv-map-inv-compute-fiber-comp g h
                ( f (vertical-map-cone f g lower x)))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f
                ( g ∘ h)
                ( pasting-vertical-cone f g h lower upper)
                ( pb-rect)
                ( vertical-map-cone f g lower x)))
            ( x , refl))

  abstract
    is-pullback-rectangle-is-pullback-top-square :
      is-pullback f g lower →
      is-pullback (horizontal-map-cone f g lower) h upper →
      is-pullback f (g ∘ h) (pasting-vertical-cone f g h lower upper)
    is-pullback-rectangle-is-pullback-top-square pb-lower pb-upper =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( f)
        ( g ∘ h)
        ( pasting-vertical-cone f g h lower upper)
        ( λ x →
          is-equiv-bottom-is-equiv-top-square
            ( map-inv-compute-fiber-comp
              ( vertical-map-cone f g lower)
              ( vertical-map-cone (horizontal-map-cone f g lower) h upper)
              ( x))
            ( map-inv-compute-fiber-comp g h (f x))
            ( map-Σ
              ( λ t → fiber h (pr1 t))
              ( map-fiber-vertical-map-cone f g lower x)
              ( λ t →
                map-fiber-vertical-map-cone
                  ( horizontal-map-cone f g lower)
                  ( h)
                  ( upper)
                  ( pr1 t)))
            ( map-fiber-vertical-map-cone
              ( f)
              ( g ∘ h)
              ( pasting-vertical-cone f g h lower upper)
              ( x))
            ( preserves-pasting-vertical-map-fiber-vertical-map-cone
              ( f)
              ( g)
              ( h)
              ( lower)
              ( upper)
              ( x))
            ( is-equiv-map-inv-compute-fiber-comp
              ( vertical-map-cone f g lower)
              ( vertical-map-cone (horizontal-map-cone f g lower) h upper)
              ( x))
            ( is-equiv-map-inv-compute-fiber-comp g h (f x))
            ( is-equiv-map-Σ
              ( λ t → fiber h (pr1 t))
              ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
                ( f)
                ( g)
                ( lower)
                ( pb-lower)
                ( x))
              ( λ t →
                is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
                  ( horizontal-map-cone f g lower)
                  ( h)
                  ( upper)
                  ( pb-upper)
                  ( pr1 t))))
```

### Triangles of pullback squares

Given a triangle of squares where the back right square is a pullback,

```text
          •
        ∧ | \
       /  |  \
      /   |   ∨
    • --------> •
    |     |     |
    |     ∨     |
    |     •     |
    |   ∧   \   |
    |  /     \  |
    ∨ /       ∨ ∨
    • --------> •
```

then the back left square is a pullback if and only if the front square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) (k : X → Z)
  (back-right : cone j h B)
  (back-left : cone i (vertical-map-cone j h back-right) A)
  (front : cone k h A)
  (K : coherence-triangle-maps' k j i)
  (H :
    htpy-parallel-cone
      ( K)
      ( refl-htpy' h)
      ( pasting-horizontal-cone i j h back-right back-left)
      ( front))
  where

  abstract
    is-pullback-front-square-horizontal-triangle :
      is-pullback j h back-right →
      is-pullback i (vertical-map-cone j h back-right) back-left →
      is-pullback k h front
    is-pullback-front-square-horizontal-triangle pb-back-right pb-back-left =
      is-pullback-htpy'
        ( K)
        ( refl-htpy' h)
        ( pasting-horizontal-cone i j h back-right back-left)
        ( H)
        ( is-pullback-rectangle-is-pullback-left-square i j h
          ( back-right)
          ( back-left)
          ( pb-back-right)
          ( pb-back-left))

  abstract
    is-pullback-left-square-horizontal-triangle :
      is-pullback j h back-right →
      is-pullback k h front →
      is-pullback i (vertical-map-cone j h back-right) back-left
    is-pullback-left-square-horizontal-triangle pb-back-right pb-front =
      is-pullback-left-square-is-pullback-rectangle i j h back-right back-left
        ( pb-back-right)
        ( is-pullback-htpy K (refl-htpy' h) front H pb-front)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z) (k : X → Z)
  (back-right : cone j h B)
  (back-left : cone i (vertical-map-cone j h back-right) A)
  (front : cone k h A)
  (K : k ~ j ∘ i)
  (H :
    htpy-parallel-cone
      ( K)
      ( refl-htpy' h)
      ( front)
      ( pasting-horizontal-cone i j h back-right back-left))
  where

  abstract
    is-pullback-front-square-horizontal-triangle' :
      is-pullback j h back-right →
      is-pullback i (vertical-map-cone j h back-right) back-left →
      is-pullback k h front
    is-pullback-front-square-horizontal-triangle' pb-back-right pb-back-left =
      is-pullback-htpy
        ( K)
        ( refl-htpy' h)
        ( pasting-horizontal-cone i j h back-right back-left)
        ( H)
        ( is-pullback-rectangle-is-pullback-left-square i j h
          ( back-right)
          ( back-left)
          ( pb-back-right)
          ( pb-back-left))

  abstract
    is-pullback-left-square-horizontal-triangle' :
      is-pullback j h back-right →
      is-pullback k h front →
      is-pullback i (vertical-map-cone j h back-right) back-left
    is-pullback-left-square-horizontal-triangle' pb-back-right pb-front =
      is-pullback-left-square-is-pullback-rectangle i j h
        ( back-right)
        ( back-left)
        ( pb-back-right)
        ( is-pullback-htpy' K (refl-htpy' h) front H pb-front)
```

We can also glue along horizontal maps.

Given a triangle of squares where the right square is a pullback,

```text
         αX
  • -----------> •
   \  ⟍           \   ⟍
    \    ↘          \    ↘
     \     • ------- \ --> •
      \   / ⌟         \   /
       ∨ ∨             ∨ ∨
        • ------------> •
```

then the left square is a pullback if and only if the top square is.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y) (k : X → Z)
  (right : cone f g B) (top : cone (horizontal-map-cone f g right) h A)
  (left : cone f k A)
  (K : g ∘ h ~ k)
  (H :
    htpy-parallel-cone
      ( refl-htpy' f)
      ( K)
      ( pasting-vertical-cone f g h right top)
      ( left))
  where

  abstract
    is-pullback-left-square-vertical-triangle :
      is-pullback f g right →
      is-pullback (horizontal-map-cone f g right) h top →
      is-pullback f k left
    is-pullback-left-square-vertical-triangle pb-right pb-top =
      is-pullback-htpy'
        ( refl-htpy' f)
        ( K)
        ( pasting-vertical-cone f g h right top)
        ( H)
        ( is-pullback-rectangle-is-pullback-top-square f g h right top
          ( pb-right)
          ( pb-top))

  abstract
    is-pullback-top-square-vertical-triangle :
      is-pullback f g right →
      is-pullback f k left →
      is-pullback (horizontal-map-cone f g right) h top
    is-pullback-top-square-vertical-triangle pb-right pb-left =
      is-pullback-top-square-is-pullback-rectangle f g h right top
        ( pb-right)
        ( is-pullback-htpy
          ( refl-htpy' f)
          ( K)
          ( left)
          ( H)
          ( pb-left))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y) (k : X → Z)
  (right : cone f g B) (top : cone (horizontal-map-cone f g right) h A)
  (left : cone f k A)
  (K : k ~ g ∘ h)
  (H :
    htpy-parallel-cone
      ( refl-htpy' f)
      ( K)
      ( left)
      ( pasting-vertical-cone f g h right top))
  where

  abstract
    is-pullback-left-square-vertical-triangle' :
      is-pullback f g right →
      is-pullback (horizontal-map-cone f g right) h top →
      is-pullback f k left
    is-pullback-left-square-vertical-triangle' pb-right pb-top =
      is-pullback-htpy
        ( refl-htpy' f)
        ( K)
        ( pasting-vertical-cone f g h right top)
        ( H)
        ( is-pullback-rectangle-is-pullback-top-square f g h right top
          ( pb-right)
          ( pb-top))

  abstract
    is-pullback-top-square-vertical-triangle' :
      is-pullback f g right →
      is-pullback f k left →
      is-pullback (horizontal-map-cone f g right) h top
    is-pullback-top-square-vertical-triangle' pb-right pb-left =
      is-pullback-top-square-is-pullback-rectangle f g h right top
        ( pb-right)
        ( is-pullback-htpy'
          ( refl-htpy' f)
          ( K)
          ( left)
          ( H)
          ( pb-left))
```

### Pullbacks are associative

Consider two cospans with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

and with pullback cones `α` and `β` respectively. Moreover, consider a cone `γ`
over the pullbacks as in the following diagram

```text
  ∙ ------------> ∙ ------------> C
  |               | ⌟             |
  |       γ       |       β       | i
  ∨               ∨               ∨
  ∙ ------------> B ------------> Y
  | ⌟             |       h
  |       α       | g
  ∨               ∨
  A ------------> X.
          f
```

Then the pasting `γ □ α` is a pullback if and only if `γ` is if and only if the
pasting `γ □ β` is. And, in particular, we have the equivalence

$$
(A ×_X B) ×_Y C ≃ A ×_X (B ×_Y C).
$$

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  {S : UU l6} {T : UU l7} {U : UU l8}
  (α : cone f g S) (β : cone h i T)
  (γ : cone (horizontal-map-cone f g α) (vertical-map-cone h i β) U)
  (is-pullback-α : is-pullback f g α)
  (is-pullback-β : is-pullback h i β)
  where

  is-pullback-associative :
    is-pullback
      ( f)
      ( g ∘ vertical-map-cone h i β)
      ( pasting-vertical-cone f g (vertical-map-cone h i β) α γ) →
    is-pullback
      ( h ∘ horizontal-map-cone f g α)
      ( i)
      ( pasting-horizontal-cone (horizontal-map-cone f g α) h i β γ)
  is-pullback-associative H =
    is-pullback-rectangle-is-pullback-left-square
      ( horizontal-map-cone f g α)
      ( h)
      ( i)
      ( β)
      ( γ)
      ( is-pullback-β)
      ( is-pullback-top-square-is-pullback-rectangle
        ( f)
        ( g)
        ( vertical-map-cone h i β)
        ( α)
        ( γ)
        ( is-pullback-α)
        ( H))

  is-pullback-inv-associative :
    is-pullback
      ( h ∘ horizontal-map-cone f g α)
      ( i)
      ( pasting-horizontal-cone (horizontal-map-cone f g α) h i β γ) →
    is-pullback
      ( f)
      ( g ∘ vertical-map-cone h i β)
      ( pasting-vertical-cone f g (vertical-map-cone h i β) α γ)
  is-pullback-inv-associative H =
    is-pullback-rectangle-is-pullback-top-square
        ( f)
        ( g)
        ( vertical-map-cone h i β)
        ( α)
        ( γ)
        ( is-pullback-α)
        ( is-pullback-left-square-is-pullback-rectangle
          ( horizontal-map-cone f g α)
          ( h)
          ( i)
          ( β)
          ( γ)
          ( is-pullback-β)
          ( H))
```

### Pullbacks can be "folded"

Given a pullback square

```text
         f'
    C -------> B
    | ⌟        |
  g'|          | g
    ∨          ∨
    A -------> X
         f
```

we can "fold" the vertical edge onto the horizontal one and get a new pullback
square

```text
            C ---------> X
            | ⌟          |
  (f' , g') |            |
            ∨            ∨
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
      is-pullback (map-product f g) (diagonal-product X) (fold-cone f g c)
    is-pullback-fold-cone-is-pullback c pb-c =
      is-equiv-left-map-triangle
        ( gap (map-product f g) (diagonal-product X) (fold-cone f g c))
        ( map-fold-cone-standard-pullback f g)
        ( gap f g c)
        ( triangle-map-fold-cone-standard-pullback f g c)
        ( pb-c)
        ( is-equiv-map-fold-cone-standard-pullback f g)

  abstract
    is-pullback-is-pullback-fold-cone :
      {l4 : Level} {C : UU l4} (c : cone f g C) →
      is-pullback (map-product f g) (diagonal-product X) (fold-cone f g c) →
      is-pullback f g c
    is-pullback-is-pullback-fold-cone c =
      is-equiv-top-map-triangle
        ( gap (map-product f g) (diagonal-product X) (fold-cone f g c))
        ( map-fold-cone-standard-pullback f g)
        ( gap f g c)
        ( triangle-map-fold-cone-standard-pullback f g c)
        ( is-equiv-map-fold-cone-standard-pullback f g)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
