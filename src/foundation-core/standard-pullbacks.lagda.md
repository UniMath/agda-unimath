# Standard pullbacks

```agda
module foundation-core.standard-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Given a [cospan of types](foundation.cospans.md)

```text
  f : A → X ← B : g,
```

we can form the
{{#concept "standard pullback" Disambiguation="types" Agda=standard-pullback}}
`A ×_X B` satisfying
[the universal property of the pullback](foundation-core.universal-property-pullbacks.md)
of the cospan, completing the diagram

```text
  A ×_X B ------> B
     | ⌟          |
     |            | g
     |            |
     v            v
     A ---------> X.
           f
```

The standard pullback consists of [pairs](foundation.dependent-pair-types.md)
`a : A` and `b : B` such that `f a` and `g b` agree:

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b).
```

Thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
the canonical projections.

## Definitions

### The standard pullback of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  standard-pullback : UU (l1 ⊔ l2 ⊔ l3)
  standard-pullback = Σ A (λ x → Σ B (λ y → f x ＝ g y))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where

  vertical-map-standard-pullback : standard-pullback f g → A
  vertical-map-standard-pullback = pr1

  horizontal-map-standard-pullback : standard-pullback f g → B
  horizontal-map-standard-pullback t = pr1 (pr2 t)

  coherence-square-standard-pullback :
    coherence-square-maps
      horizontal-map-standard-pullback
      vertical-map-standard-pullback
      g
      f
  coherence-square-standard-pullback t = pr2 (pr2 t)
```

### The cone at the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  cone-standard-pullback : cone f g (standard-pullback f g)
  pr1 cone-standard-pullback = vertical-map-standard-pullback
  pr1 (pr2 cone-standard-pullback) = horizontal-map-standard-pullback
  pr2 (pr2 cone-standard-pullback) = coherence-square-standard-pullback
```

### The gap map into the standard pullback

The {{#concept "standard gap map" Disambiguation="cone over a cospan" Agda=gap}}
of a [commuting square](foundation-core.commuting-squares-of-maps.md) is the map
from the domain of the cone into the standard pullback.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  gap : cone f g C → C → standard-pullback f g
  pr1 (gap c z) = vertical-map-cone f g c z
  pr1 (pr2 (gap c z)) = horizontal-map-cone f g c z
  pr2 (pr2 (gap c z)) = coherence-square-cone f g c z
```

## Properties

### Characterization of the identity type of the standard pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-standard-pullback : (t t' : standard-pullback f g) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-standard-pullback (a , b , p) (a' , b' , p') =
    Σ (a ＝ a') (λ α → Σ (b ＝ b') (λ β → ap f α ∙ p' ＝ p ∙ ap g β))

  refl-Eq-standard-pullback :
    (t : standard-pullback f g) → Eq-standard-pullback t t
  pr1 (refl-Eq-standard-pullback (a , b , p)) = refl
  pr1 (pr2 (refl-Eq-standard-pullback (a , b , p))) = refl
  pr2 (pr2 (refl-Eq-standard-pullback (a , b , p))) = inv right-unit

  Eq-eq-standard-pullback :
    (s t : standard-pullback f g) → s ＝ t → Eq-standard-pullback s t
  Eq-eq-standard-pullback s .s refl = refl-Eq-standard-pullback s

  extensionality-standard-pullback :
    (t t' : standard-pullback f g) → (t ＝ t') ≃ Eq-standard-pullback t t'
  extensionality-standard-pullback (a , b , p) =
    extensionality-Σ
      ( λ bp' α → Σ (b ＝ pr1 bp') (λ β → ap f α ∙ pr2 bp' ＝ p ∙ ap g β))
      ( refl)
      ( refl , inv right-unit)
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ p' β → p' ＝ p ∙ ap g β)
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-standard-pullback :
    { s t : standard-pullback f g}
    ( α : vertical-map-standard-pullback s ＝ vertical-map-standard-pullback t)
    ( β :
      horizontal-map-standard-pullback s ＝
      horizontal-map-standard-pullback t) →
    ( ( ap f α ∙ coherence-square-standard-pullback t) ＝
      ( coherence-square-standard-pullback s ∙ ap g β)) →
    s ＝ t
  map-extensionality-standard-pullback {s} {t} α β γ =
    map-inv-equiv (extensionality-standard-pullback s t) (α , β , γ)
```

### The standard pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-standard-pullback :
      universal-property-pullback f g (cone-standard-pullback f g)
    universal-property-standard-pullback C =
      is-equiv-comp
        ( tot (λ _ → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv (λ _ → is-equiv-map-distributive-Π-Σ))
```

### A cone is equal to the value of `cone-map` at its own gap map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X)
  where

  htpy-cone-up-pullback-standard-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-standard-pullback f g) (gap f g c)) c
  pr1 (htpy-cone-up-pullback-standard-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-standard-pullback c)) = right-unit-htpy
```

### The standard pullback of a Σ-type

Squares of the form

```text
  Σ (x : A) (Q (f x)) ----> Σ (y : B) Q
      |                          |
      |                          |
  pr1 |                          | pr1
      |                          |
      V                          V
      A -----------------------> B
                   f
```

are pullbacks.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  standard-pullback-Σ : UU (l1 ⊔ l3)
  standard-pullback-Σ = Σ A (λ x → Q (f x))

  cone-standard-pullback-Σ : cone f pr1 standard-pullback-Σ
  pr1 cone-standard-pullback-Σ = pr1
  pr1 (pr2 cone-standard-pullback-Σ) = map-Σ-map-base f Q
  pr2 (pr2 cone-standard-pullback-Σ) = refl-htpy

  inv-gap-cone-standard-pullback-Σ :
    standard-pullback f (pr1 {B = Q}) → standard-pullback-Σ
  pr1 (inv-gap-cone-standard-pullback-Σ (x , _)) = x
  pr2 (inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl)) = q

  abstract
    is-section-inv-gap-cone-standard-pullback-Σ :
      is-section
        ( gap f pr1 cone-standard-pullback-Σ)
        ( inv-gap-cone-standard-pullback-Σ)
    is-section-inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl) = refl

  abstract
    is-retraction-inv-gap-cone-standard-pullback-Σ :
      is-retraction
        ( gap f pr1 cone-standard-pullback-Σ)
        ( inv-gap-cone-standard-pullback-Σ)
    is-retraction-inv-gap-cone-standard-pullback-Σ = refl-htpy

  abstract
    is-pullback-cone-standard-pullback-Σ :
      is-equiv (gap f pr1 cone-standard-pullback-Σ)
    is-pullback-cone-standard-pullback-Σ =
      is-equiv-is-invertible
        inv-gap-cone-standard-pullback-Σ
        is-section-inv-gap-cone-standard-pullback-Σ
        is-retraction-inv-gap-cone-standard-pullback-Σ

  compute-standard-pullback-Σ :
    standard-pullback-Σ ≃ standard-pullback f pr1
  pr1 compute-standard-pullback-Σ = gap f pr1 cone-standard-pullback-Σ
  pr2 compute-standard-pullback-Σ = is-pullback-cone-standard-pullback-Σ
```

### Standard pullbacks are symmetric

The standard pullback of `f : A → X ← B : g` is equivalent to the standard
pullback of `g : B → X ← A : f`.

```agda
map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → standard-pullback f g → standard-pullback g f
pr1 (map-commutative-standard-pullback f g x) =
  horizontal-map-standard-pullback x
pr1 (pr2 (map-commutative-standard-pullback f g x)) =
  vertical-map-standard-pullback x
pr2 (pr2 (map-commutative-standard-pullback f g x)) =
  inv (coherence-square-standard-pullback x)

inv-inv-map-commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  ( map-commutative-standard-pullback f g ∘
    map-commutative-standard-pullback g f) ~ id
inv-inv-map-commutative-standard-pullback f g x =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber
      ( inv-inv (coherence-square-standard-pullback x)))

abstract
  is-equiv-map-commutative-standard-pullback :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
    (f : A → X) (g : B → X) → is-equiv (map-commutative-standard-pullback f g)
  is-equiv-map-commutative-standard-pullback f g =
    is-equiv-is-invertible
      ( map-commutative-standard-pullback g f)
      ( inv-inv-map-commutative-standard-pullback f g)
      ( inv-inv-map-commutative-standard-pullback g f)

commutative-standard-pullback :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) →
  standard-pullback f g ≃ standard-pullback g f
pr1 (commutative-standard-pullback f g) =
  map-commutative-standard-pullback f g
pr2 (commutative-standard-pullback f g) =
  is-equiv-map-commutative-standard-pullback f g

triangle-map-commutative-standard-pullback :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (c : cone f g C) →
  gap g f (swap-cone f g c) ~
  map-commutative-standard-pullback f g ∘ gap f g c
triangle-map-commutative-standard-pullback f g c = refl-htpy
```

### Pullbacks can be "folded"

Given a standard pullback square

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

  fold-cone :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone (map-product f g) (diagonal X) C
  pr1 (pr1 (fold-cone c) z) = vertical-map-cone f g c z
  pr2 (pr1 (fold-cone c) z) = horizontal-map-cone f g c z
  pr1 (pr2 (fold-cone c)) = g ∘ horizontal-map-cone f g c
  pr2 (pr2 (fold-cone c)) z = eq-pair (coherence-square-cone f g c z) refl

  map-fold-cone-standard-pullback :
    standard-pullback f g → standard-pullback (map-product f g) (diagonal X)
  pr1 (pr1 (map-fold-cone-standard-pullback x)) =
    vertical-map-standard-pullback x
  pr2 (pr1 (map-fold-cone-standard-pullback x)) =
    horizontal-map-standard-pullback x
  pr1 (pr2 (map-fold-cone-standard-pullback x)) =
    g (horizontal-map-standard-pullback x)
  pr2 (pr2 (map-fold-cone-standard-pullback x)) =
    eq-pair (coherence-square-standard-pullback x) refl

  map-inv-fold-cone-standard-pullback :
    standard-pullback (map-product f g) (diagonal X) → standard-pullback f g
  pr1 (map-inv-fold-cone-standard-pullback ((a , b) , x , α)) = a
  pr1 (pr2 (map-inv-fold-cone-standard-pullback ((a , b) , x , α))) = b
  pr2 (pr2 (map-inv-fold-cone-standard-pullback ((a , b) , x , α))) =
    ap pr1 α ∙ inv (ap pr2 α)

  abstract
    is-section-map-inv-fold-cone-standard-pullback :
      is-section
        ( map-fold-cone-standard-pullback)
        ( map-inv-fold-cone-standard-pullback)
    is-section-map-inv-fold-cone-standard-pullback ((a , b) , (x , α)) =
      map-extensionality-standard-pullback
        ( map-product f g)
        ( diagonal X)
        ( refl)
        ( ap pr2 α)
        ( ( inv (is-section-pair-eq α)) ∙
          ( ap
            ( λ t → eq-pair t (ap pr2 α))
            ( ( inv right-unit) ∙
              ( inv
                ( left-whisker-concat
                  ( ap pr1 α)
                  ( left-inv (ap pr2 α)))) ∙
              ( inv (assoc (ap pr1 α) (inv (ap pr2 α)) (ap pr2 α))))) ∙
          ( eq-pair-concat
            ( ap pr1 α ∙ inv (ap pr2 α))
            ( ap pr2 α)
            ( refl)
            ( ap pr2 α)) ∙
          ( ap
            ( concat (eq-pair (ap pr1 α ∙ inv (ap pr2 α)) refl) (x , x))
            ( inv (ap-diagonal (ap pr2 α)))))

  abstract
    is-retraction-map-inv-fold-cone-standard-pullback :
      is-retraction
        ( map-fold-cone-standard-pullback)
        ( map-inv-fold-cone-standard-pullback)
    is-retraction-map-inv-fold-cone-standard-pullback (a , b , p) =
      map-extensionality-standard-pullback f g
        ( refl)
        ( refl)
        ( inv
          ( ( right-whisker-concat
              ( ( right-whisker-concat
                  ( ap-pr1-eq-pair p refl)
                  ( inv (ap pr2 (eq-pair p refl)))) ∙
                ( ap (λ t → p ∙ inv t) (ap-pr2-eq-pair p refl)) ∙
                ( right-unit))
              ( refl)) ∙
            ( right-unit)))

  abstract
    is-equiv-map-fold-cone-standard-pullback :
      is-equiv map-fold-cone-standard-pullback
    is-equiv-map-fold-cone-standard-pullback =
      is-equiv-is-invertible
        ( map-inv-fold-cone-standard-pullback)
        ( is-section-map-inv-fold-cone-standard-pullback)
        ( is-retraction-map-inv-fold-cone-standard-pullback)

  triangle-map-fold-cone-standard-pullback :
    {l4 : Level} {C : UU l4} (c : cone f g C) →
    gap (map-product f g) (diagonal X) (fold-cone c) ~
    map-fold-cone-standard-pullback ∘ gap f g c
  triangle-map-fold-cone-standard-pullback c = refl-htpy
```

### Products of standard pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  map-product-cone-standard-pullback :
    (standard-pullback f g) × (standard-pullback f' g') →
    standard-pullback (map-product f f') (map-product g g')
  map-product-cone-standard-pullback =
    ( tot
      ( λ t →
        ( tot (λ s → eq-pair')) ∘
        ( map-interchange-Σ-Σ (λ y p y' → f' (pr2 t) ＝ g' y')))) ∘
    ( map-interchange-Σ-Σ (λ x t x' → Σ B' (λ y' → f' x' ＝ g' y')))

  abstract
    is-equiv-map-product-cone-standard-pullback :
      is-equiv map-product-cone-standard-pullback
    is-equiv-map-product-cone-standard-pullback =
      is-equiv-comp
        ( tot (λ t → tot (λ s → eq-pair') ∘ map-interchange-Σ-Σ _))
        ( map-interchange-Σ-Σ _)
        ( is-equiv-map-interchange-Σ-Σ _)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ t →
            is-equiv-comp
              ( tot (λ s → eq-pair'))
              ( map-interchange-Σ-Σ (λ y p y' → f' (pr2 t) ＝ g' y'))
              ( is-equiv-map-interchange-Σ-Σ _)
              ( is-equiv-tot-is-fiberwise-equiv
                ( λ s →
                  is-equiv-eq-pair (map-product f f' t) (map-product g g' s)))))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
