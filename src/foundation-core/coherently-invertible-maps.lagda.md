# Coherently invertible maps

```agda
module foundation-core.coherently-invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

An [inverse](foundation-core.invertible-maps.md) for a map `f : A → B` is a map
`g : B → A` equipped with [homotopies](foundation-core.homotopies.md)
` (f ∘ g) ~ id` and `(g ∘ f) ~ id`. Such data, however is
[structure](foundation.structure.md) on the map `f`, and not generally a
[property](foundation-core.propositions.md). Therefore we include a coherence
condition for the homotopies of an inverse. A **coherently invertible map**
`f : A → B` is a map equipped with a two-sided inverse and this additional
coherence law. They are also called half-adjoint equivalences.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

  is-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-coherently-invertible f =
    Σ ( B → A)
      ( λ g → Σ ((f ∘ g) ~ id)
        ( λ G → Σ ((g ∘ f) ~ id)
          ( λ H → coherence-is-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f)
  where

  map-inv-is-coherently-invertible : B → A
  map-inv-is-coherently-invertible = pr1 H

  is-retraction-is-coherently-invertible :
    (f ∘ map-inv-is-coherently-invertible) ~ id
  is-retraction-is-coherently-invertible = pr1 (pr2 H)

  is-section-is-coherently-invertible :
    (map-inv-is-coherently-invertible ∘ f) ~ id
  is-section-is-coherently-invertible = pr1 (pr2 (pr2 H))

  coh-is-coherently-invertible :
    coherence-is-coherently-invertible f
      ( map-inv-is-coherently-invertible)
      ( is-retraction-is-coherently-invertible)
      ( is-section-is-coherently-invertible)
  coh-is-coherently-invertible = pr2 (pr2 (pr2 H))

  is-invertible-is-coherently-invertible : is-invertible f
  pr1 is-invertible-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr1 (pr2 is-invertible-is-coherently-invertible) =
    is-retraction-is-coherently-invertible
  pr2 (pr2 is-invertible-is-coherently-invertible) =
    is-section-is-coherently-invertible

  section-is-coherently-invertible : section f
  pr1 section-is-coherently-invertible = map-inv-is-coherently-invertible
  pr2 section-is-coherently-invertible = is-retraction-is-coherently-invertible

  retraction-is-coherently-invertible : retraction f
  pr1 retraction-is-coherently-invertible = map-inv-is-coherently-invertible
  pr2 retraction-is-coherently-invertible = is-section-is-coherently-invertible
```

## Properties

### Invertible maps are coherently invertible

#### Lemma: A coherence for homotopies to an identity map

```agda
coh-is-coherently-invertible-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ (λ x → x)) →
  (x : A) → H (f x) ＝ ap f (H x)
coh-is-coherently-invertible-id {_} {A} {f} H x =
  is-injective-concat' (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( nat-htpy H (H x)))
```

#### The proof that invertible maps are coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-section-map-inv-is-invertible :
      (H : is-invertible f) → (f ∘ map-inv-is-invertible H) ~ id
    is-section-map-inv-is-invertible H y =
      ( inv (is-retraction-is-invertible H (f (map-inv-is-invertible H y)))) ∙
      ( ( ap f (is-section-is-invertible H (map-inv-is-invertible H y))) ∙
        ( is-retraction-is-invertible H y))

    is-retraction-map-inv-is-invertible :
      (H : is-invertible f) → (map-inv-is-invertible H ∘ f) ~ id
    is-retraction-map-inv-is-invertible = is-section-is-invertible

    coherence-map-inv-is-invertible :
      ( H : is-invertible f) →
      ( is-section-map-inv-is-invertible H ·r f) ~
      ( f ·l is-retraction-map-inv-is-invertible H)
    coherence-map-inv-is-invertible H x =
      inv
        ( left-transpose-eq-concat
          ( is-retraction-is-invertible H (f (map-inv-is-invertible H (f x))))
          ( ap f (is-section-is-invertible H x))
          ( ( ap f
              ( is-section-is-invertible H (map-inv-is-invertible H (f x)))) ∙
            ( is-retraction-is-invertible H (f x)))
          ( coherence-square-identifications-top-paste
            ( is-retraction-is-invertible H (f (map-inv-is-invertible H (f x))))
            ( ap f (is-section-is-invertible H x))
            ( ( ap
                ( f ∘ (map-inv-is-invertible H ∘ f))
                ( is-section-is-invertible H x)))
            ( is-retraction-is-invertible H (f x))
            ( ( ap-comp f
                ( map-inv-is-invertible H ∘ f)
                ( is-section-is-invertible H x)) ∙
              ( inv
                ( ap
                  ( ap f)
                  ( coh-is-coherently-invertible-id
                    ( is-section-is-invertible H) x))))
            ( nat-htpy
              ( htpy-right-whisk (is-retraction-is-invertible H) f)
              ( is-section-is-invertible H x))))

  abstract
    is-coherently-invertible-is-invertible :
      (H : is-invertible f) → is-coherently-invertible f
    pr1 (is-coherently-invertible-is-invertible H) =
      map-inv-is-invertible H
    pr1 (pr2 (is-coherently-invertible-is-invertible H)) =
      is-section-map-inv-is-invertible H
    pr1 (pr2 (pr2 (is-coherently-invertible-is-invertible H))) =
      is-retraction-map-inv-is-invertible H
    pr2 (pr2 (pr2 (is-coherently-invertible-is-invertible H))) =
      coherence-map-inv-is-invertible H
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
