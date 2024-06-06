# Dependent products of pullbacks

```agda
module foundation.dependent-products-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

Given a family of pullback squares

```text
    Cᵢ ─────> Bᵢ
    │ ⌟       │
    │         │ gᵢ
    ∨         ∨
    Aᵢ ─────> Xᵢ
         fᵢ
```

indexed by `i : I`, their dependent product

```text
  Πᵢ Cᵢ ─────> Πᵢ Bᵢ
    │ ⌟          │
    │            │ Πᵢ gᵢ
    ∨            ∨
  Πᵢ Aᵢ ─────> Πᵢ Xᵢ
         Πᵢ fᵢ
```

is again a pullback square.

## Definitions

### Dependent products of cones

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i))
  where

  cone-Π : cone (map-Π f) (map-Π g) ((i : I) → C i)
  pr1 cone-Π = map-Π (λ i → pr1 (c i))
  pr1 (pr2 cone-Π) = map-Π (λ i → pr1 (pr2 (c i)))
  pr2 (pr2 cone-Π) = htpy-map-Π (λ i → pr2 (pr2 (c i)))
```

## Properties

### Computing the standard pullback of a dependent product

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

  map-inv-standard-pullback-Π :
    ((i : I) → standard-pullback (f i) (g i)) →
    standard-pullback (map-Π f) (map-Π g)
  pr1 (map-inv-standard-pullback-Π h) i = pr1 (h i)
  pr1 (pr2 (map-inv-standard-pullback-Π h)) i = pr1 (pr2 (h i))
  pr2 (pr2 (map-inv-standard-pullback-Π h)) = eq-htpy (λ i → pr2 (pr2 (h i)))

  abstract
    is-section-map-inv-standard-pullback-Π :
      is-section (map-standard-pullback-Π) (map-inv-standard-pullback-Π)
    is-section-map-inv-standard-pullback-Π h =
      eq-htpy
        ( λ i →
          map-extensionality-standard-pullback (f i) (g i) refl refl
            ( inv
              ( ( right-unit) ∙
                ( htpy-eq (is-section-eq-htpy (λ i → pr2 (pr2 (h i)))) i))))

  abstract
    is-retraction-map-inv-standard-pullback-Π :
      is-retraction (map-standard-pullback-Π) (map-inv-standard-pullback-Π)
    is-retraction-map-inv-standard-pullback-Π (α , β , γ) =
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
        ( map-inv-standard-pullback-Π)
        ( is-section-map-inv-standard-pullback-Π)
        ( is-retraction-map-inv-standard-pullback-Π)

  compute-standard-pullback-Π :
    ( standard-pullback (map-Π f) (map-Π g)) ≃
    ( (i : I) → standard-pullback (f i) (g i))
  compute-standard-pullback-Π =
    map-standard-pullback-Π , is-equiv-map-standard-pullback-Π
```

### A dependent product of gap maps computes as the gap map of the dependent product

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i))
  where

  triangle-map-standard-pullback-Π :
    map-Π (λ i → gap (f i) (g i) (c i)) ~
    map-standard-pullback-Π f g ∘ gap (map-Π f) (map-Π g) (cone-Π f g c)
  triangle-map-standard-pullback-Π h =
    eq-htpy
      ( λ i →
        map-extensionality-standard-pullback
          ( f i)
          ( g i)
          ( refl)
          ( refl)
          ( htpy-eq (is-section-eq-htpy _) i ∙ inv right-unit))
```

### Dependent products of pullbacks are pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4} {C : I → UU l5}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  (c : (i : I) → cone (f i) (g i) (C i))
  where

  abstract
    is-pullback-Π :
      ((i : I) → is-pullback (f i) (g i) (c i)) →
      is-pullback (map-Π f) (map-Π g) (cone-Π f g c)
    is-pullback-Π is-pb-c =
      is-equiv-top-map-triangle
        ( map-Π (λ i → gap (f i) (g i) (c i)))
        ( map-standard-pullback-Π f g)
        ( gap (map-Π f) (map-Π g) (cone-Π f g c))
        ( triangle-map-standard-pullback-Π f g c)
        ( is-equiv-map-standard-pullback-Π f g)
        ( is-equiv-map-Π-is-fiberwise-equiv is-pb-c)
```

### Cones satisfying the universal property of pullbacks are closed under dependent products

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1}
  {A : I → UU l2} {B : I → UU l3} {X : I → UU l4}
  (f : (i : I) → A i → X i) (g : (i : I) → B i → X i)
  {C : I → UU l5} (c : (i : I) → cone (f i) (g i) (C i))
  where

  universal-property-pullback-Π :
    ((i : I) → universal-property-pullback (f i) (g i) (c i)) →
    universal-property-pullback (map-Π f) (map-Π g) (cone-Π f g c)
  universal-property-pullback-Π H =
    universal-property-pullback-is-pullback
      ( map-Π f)
      ( map-Π g)
      ( cone-Π f g c)
      ( is-pullback-Π f g c
        ( λ i →
          is-pullback-universal-property-pullback (f i) (g i) (c i) (H i)))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
