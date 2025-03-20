# Standard pullbacks

```agda
open import foundation.function-extensionality-axiom

module
  foundation.standard-pullbacks
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types funext
open import foundation.identity-types funext
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps funext
open import foundation-core.diagonal-maps-cartesian-products-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks funext
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
     ∨            ∨
     A ---------> X.
           f
```

The standard pullback consists of [pairs](foundation.dependent-pair-types.md)
`a : A` and `b : B` such that `f a` and `g b` agree:

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b),
```

thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
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
      ( horizontal-map-standard-pullback)
      ( vertical-map-standard-pullback)
      ( g)
      ( f)
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

  coherence-Eq-standard-pullback :
    (t t' : standard-pullback f g) →
    vertical-map-standard-pullback t ＝
    vertical-map-standard-pullback t' →
    horizontal-map-standard-pullback t ＝
    horizontal-map-standard-pullback t' →
    UU l3
  coherence-Eq-standard-pullback (a , b , p) (a' , b' , p') α β =
    ap f α ∙ p' ＝ p ∙ ap g β

  Eq-standard-pullback : (t t' : standard-pullback f g) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-standard-pullback (a , b , p) (a' , b' , p') =
    Σ ( a ＝ a')
      ( λ α →
        Σ ( b ＝ b')
          ( coherence-Eq-standard-pullback (a , b , p) (a' , b' , p') α))

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

  eq-Eq-standard-pullback :
    { s t : standard-pullback f g}
    ( α : vertical-map-standard-pullback s ＝ vertical-map-standard-pullback t)
    ( β :
      horizontal-map-standard-pullback s ＝
      horizontal-map-standard-pullback t) →
    ( ( ap f α ∙ coherence-square-standard-pullback t) ＝
      ( coherence-square-standard-pullback s ∙ ap g β)) →
    s ＝ t
  eq-Eq-standard-pullback {s} {t} α β γ =
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

### Pullbacks can be "folded"

Given a standard pullback square

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

  fold-cone :
    {l4 : Level} {C : UU l4} →
    cone f g C → cone (map-product f g) (diagonal-product X) C
  pr1 (pr1 (fold-cone c) z) = vertical-map-cone f g c z
  pr2 (pr1 (fold-cone c) z) = horizontal-map-cone f g c z
  pr1 (pr2 (fold-cone c)) = g ∘ horizontal-map-cone f g c
  pr2 (pr2 (fold-cone c)) z = eq-pair (coherence-square-cone f g c z) refl

  map-fold-cone-standard-pullback :
    standard-pullback f g →
    standard-pullback (map-product f g) (diagonal-product X)
  pr1 (pr1 (map-fold-cone-standard-pullback x)) =
    vertical-map-standard-pullback x
  pr2 (pr1 (map-fold-cone-standard-pullback x)) =
    horizontal-map-standard-pullback x
  pr1 (pr2 (map-fold-cone-standard-pullback x)) =
    g (horizontal-map-standard-pullback x)
  pr2 (pr2 (map-fold-cone-standard-pullback x)) =
    eq-pair (coherence-square-standard-pullback x) refl

  map-inv-fold-cone-standard-pullback :
    standard-pullback (map-product f g) (diagonal-product X) →
    standard-pullback f g
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
      eq-Eq-standard-pullback
        ( map-product f g)
        ( diagonal-product X)
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
            ( inv (compute-ap-diagonal-product (ap pr2 α)))))

  abstract
    is-retraction-map-inv-fold-cone-standard-pullback :
      is-retraction
        ( map-fold-cone-standard-pullback)
        ( map-inv-fold-cone-standard-pullback)
    is-retraction-map-inv-fold-cone-standard-pullback (a , b , p) =
      eq-Eq-standard-pullback f g
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

  compute-fold-standard-pullback :
    standard-pullback f g ≃
    standard-pullback (map-product f g) (diagonal-product X)
  compute-fold-standard-pullback =
    map-fold-cone-standard-pullback , is-equiv-map-fold-cone-standard-pullback

  triangle-map-fold-cone-standard-pullback :
    {l4 : Level} {C : UU l4} (c : cone f g C) →
    gap (map-product f g) (diagonal-product X) (fold-cone c) ~
    map-fold-cone-standard-pullback ∘ gap f g c
  triangle-map-fold-cone-standard-pullback c = refl-htpy
```

### The equivalence on standard pullbacks induced by parallel cospans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f f' : A → X} (Hf : f ~ f') {g g' : B → X} (Hg : g ~ g')
  where

  map-equiv-standard-pullback-htpy :
    standard-pullback f' g' → standard-pullback f g
  map-equiv-standard-pullback-htpy =
    tot (λ a → tot (λ b → concat' (f a) (inv (Hg b)) ∘ concat (Hf a) (g' b)))

  abstract
    is-equiv-map-equiv-standard-pullback-htpy :
      is-equiv map-equiv-standard-pullback-htpy
    is-equiv-map-equiv-standard-pullback-htpy =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a →
          is-equiv-tot-is-fiberwise-equiv
            ( λ b →
              is-equiv-comp
                ( concat' (f a) (inv (Hg b)))
                ( concat (Hf a) (g' b))
                ( is-equiv-concat (Hf a) (g' b))
                ( is-equiv-concat' (f a) (inv (Hg b)))))

  equiv-standard-pullback-htpy :
    standard-pullback f' g' ≃ standard-pullback f g
  pr1 equiv-standard-pullback-htpy = map-equiv-standard-pullback-htpy
  pr2 equiv-standard-pullback-htpy = is-equiv-map-equiv-standard-pullback-htpy
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
