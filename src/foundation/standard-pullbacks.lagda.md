# Standard pullbacks

```agda
module foundation.standard-pullbacks where

open import foundation-core.standard-pullbacks public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.descent-equivalences
open import foundation.equality-coproduct-types
open import foundation.function-extensionality
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.multivariable-homotopies
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.postcomposition-functions
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
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
`a : A` and `b : B` such that `f a ＝ g b` agree

```text
  A ×_X B := Σ (a : A) (b : B), (f a ＝ g b),
```

thus the standard [cone](foundation.cones-over-cospan-diagrams.md) consists of
the canonical projections.

## Properties

### Standard pullbacks are closed under exponentiation

Given a pullback square

```text
          f'
    C ---------> B
    | ⌟          |
  g'|            | g
    |            |
    v            v
    A ---------> X
          f
```

then the exponentiated square given by postcomposition

```text
                f' ∘ -
      (S → C) ---------> (S → B)
         |                  |
  g' ∘ - |                  | g ∘ -
         |                  |
         v                  v
      (S → A) ---------> (S → X)
                f ∘ -
```

is a pullback square for any type `S`.

```agda
map-standard-pullback-postcomp :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  (T : UU l4) → standard-pullback (postcomp T f) (postcomp T g) → cone f g T
map-standard-pullback-postcomp f g T = tot (λ _ → tot (λ _ → htpy-eq))

abstract
  is-equiv-map-standard-pullback-postcomp :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
    (T : UU l4) → is-equiv (map-standard-pullback-postcomp f g T)
  is-equiv-map-standard-pullback-postcomp f g T =
    is-equiv-tot-is-fiberwise-equiv
      ( λ p → is-equiv-tot-is-fiberwise-equiv (λ q → funext (f ∘ p) (g ∘ q)))

triangle-map-standard-pullback-postcomp :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (T : UU l5) (f : A → X) (g : B → X) (c : cone f g C) →
  cone-map f g c {T} ~
  map-standard-pullback-postcomp f g T ∘
  gap (postcomp T f) (postcomp T g) (postcomp-cone T f g c)
triangle-map-standard-pullback-postcomp T f g c h =
  eq-pair-eq-fiber
    ( eq-pair-eq-fiber
      ( inv (is-section-eq-htpy (coherence-square-cone f g c ·r h))))
```

### The equivalence on canonical pullbacks induced by parallel cospans

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

### Dependent products of standard pullbacks are standard pullbacks

Given a family of pullback squares, their dependent product is again a pullback
square.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  where

  map-standard-pullback-Π :
    standard-pullback (map-Π f) (map-Π g) →
    (i : I) → standard-pullback (f i) (g i)
  pr1 (map-standard-pullback-Π (α , β , γ) i) = α i
  pr1 (pr2 (map-standard-pullback-Π (α , β , γ) i)) = β i
  pr2 (pr2 (map-standard-pullback-Π (α , β , γ) i)) = htpy-eq γ i

  inv-map-standard-pullback-Π :
    ((i : I) → standard-pullback (f i) (g i)) →
    standard-pullback (map-Π f) (map-Π g)
  pr1 (inv-map-standard-pullback-Π h) i = pr1 (h i)
  pr1 (pr2 (inv-map-standard-pullback-Π h)) i = pr1 (pr2 (h i))
  pr2 (pr2 (inv-map-standard-pullback-Π h)) = eq-htpy (λ i → pr2 (pr2 (h i)))

  abstract
    is-section-inv-map-standard-pullback-Π :
      is-section (map-standard-pullback-Π) (inv-map-standard-pullback-Π)
    is-section-inv-map-standard-pullback-Π h =
      eq-htpy
        ( λ i →
          map-extensionality-standard-pullback (f i) (g i) refl refl
            ( inv
              ( ( right-unit) ∙
                ( htpy-eq (is-section-eq-htpy (λ i → pr2 (pr2 (h i)))) i))))

  abstract
    is-retraction-inv-map-standard-pullback-Π :
      is-retraction (map-standard-pullback-Π) (inv-map-standard-pullback-Π)
    is-retraction-inv-map-standard-pullback-Π (α , β , γ) =
      map-extensionality-standard-pullback
        ( map-Π f)
        ( map-Π g)
        ( refl)
        ( refl)
        ( inv (right-unit ∙ is-retraction-eq-htpy γ))

  abstract
    is-equiv-map-standard-pullback-Π :
      is-equiv (map-standard-pullback-Π)
    is-equiv-map-standard-pullback-Π =
      is-equiv-is-invertible
        ( inv-map-standard-pullback-Π)
        ( is-section-inv-map-standard-pullback-Π)
        ( is-retraction-inv-map-standard-pullback-Π)
```

### Coproducts of standard pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (f' : A' → X') (g' : B' → X')
  where

  inl-map-coproduct-cone-standard-pullback :
    standard-pullback f g →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  pr1 (inl-map-coproduct-cone-standard-pullback (x , y , p)) = inl x
  pr1 (pr2 (inl-map-coproduct-cone-standard-pullback (x , y , p))) = inl y
  pr2 (pr2 (inl-map-coproduct-cone-standard-pullback (x , y , p))) = ap inl p

  inr-map-coproduct-cone-standard-pullback :
    standard-pullback f' g' →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  pr1 (inr-map-coproduct-cone-standard-pullback (x , y , p)) = inr x
  pr1 (pr2 (inr-map-coproduct-cone-standard-pullback (x , y , p))) = inr y
  pr2 (pr2 (inr-map-coproduct-cone-standard-pullback (x , y , p))) = ap inr p

  map-coproduct-cone-standard-pullback :
    standard-pullback f g + standard-pullback f' g' →
    standard-pullback (map-coproduct f f') (map-coproduct g g')
  map-coproduct-cone-standard-pullback (inl v) =
    inl-map-coproduct-cone-standard-pullback v
  map-coproduct-cone-standard-pullback (inr u) =
    inr-map-coproduct-cone-standard-pullback u

  map-inv-coproduct-cone-standard-pullback :
    standard-pullback (map-coproduct f f') (map-coproduct g g') →
    standard-pullback f g + standard-pullback f' g'
  map-inv-coproduct-cone-standard-pullback (inl x , inl y , p) =
    inl (x , y , is-injective-inl p)
  map-inv-coproduct-cone-standard-pullback (inr x , inr y , p) =
    inr (x , y , is-injective-inr p)

  is-section-map-inv-coproduct-cone-standard-pullback :
    is-section map-coproduct-cone-standard-pullback map-inv-coproduct-cone-standard-pullback
  is-section-map-inv-coproduct-cone-standard-pullback (inl x , inl y , p) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (is-section-is-injective-inl p))
  is-section-map-inv-coproduct-cone-standard-pullback (inr x , inr y , p) =
    eq-pair-eq-fiber (eq-pair-eq-fiber (is-section-is-injective-inr p))

  is-retraction-map-inv-coproduct-cone-standard-pullback :
    is-retraction map-coproduct-cone-standard-pullback map-inv-coproduct-cone-standard-pullback
  is-retraction-map-inv-coproduct-cone-standard-pullback (inl (x , y , p)) =
    ap
      ( inl)
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (is-retraction-is-injective-inl p)))
  is-retraction-map-inv-coproduct-cone-standard-pullback (inr (x , y , p)) =
    ap
      ( inr)
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (is-retraction-is-injective-inr p)))

  abstract
    is-equiv-map-coproduct-cone-standard-pullback :
      is-equiv map-coproduct-cone-standard-pullback
    is-equiv-map-coproduct-cone-standard-pullback =
      is-equiv-is-invertible
        map-inv-coproduct-cone-standard-pullback
        is-section-map-inv-coproduct-cone-standard-pullback
        is-retraction-map-inv-coproduct-cone-standard-pullback

  triangle-map-coproduct-cone-standard-pullback :
    {l4 l4' : Level} {C : UU l4} {C' : UU l4'}
    (c : cone f g C) (c' : cone f' g' C') →
    ( gap
      ( map-coproduct f f')
      ( map-coproduct g g')
      ( coproduct-cone f g f' g' c c')) ~
    ( map-coproduct-cone-standard-pullback) ∘
    ( map-coproduct (gap f g c) (gap f' g' c'))
  triangle-map-coproduct-cone-standard-pullback c c' (inl _) =
    eq-pair-eq-fiber (eq-pair-eq-fiber right-unit)
  triangle-map-coproduct-cone-standard-pullback c c' (inr _) =
    eq-pair-eq-fiber (eq-pair-eq-fiber right-unit)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
