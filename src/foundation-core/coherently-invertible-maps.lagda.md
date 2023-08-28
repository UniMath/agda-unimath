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

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
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
  where

  inv-is-coherently-invertible : is-coherently-invertible f → B → A
  inv-is-coherently-invertible = pr1

  is-section-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
  is-section-inv-is-coherently-invertible H = pr1 (pr2 H)

  is-retraction-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
  is-retraction-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

  coh-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-coherently-invertible f
      ( inv-is-coherently-invertible H)
      ( is-section-inv-is-coherently-invertible H)
      ( is-retraction-inv-is-coherently-invertible H)
  coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))
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

#### Invertible maps are coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    coherence-map-inv-has-inverse :
      ( H : has-inverse f) →
      ( is-section-map-inv-has-inverse H ·r f) ~
      ( f ·l is-retraction-map-inv-has-inverse H)
    coherence-map-inv-has-inverse H x =
      inv
        ( inv-con
          ( pr1 (pr2 H) (f (map-inv-has-inverse H (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( ( ap f (pr2 (pr2 H) (map-inv-has-inverse H (f x)))) ∙
            ( pr1 (pr2 H) (f x)))
          ( coherence-square-identifications-top-paste
            ( pr1 (pr2 H) (f (map-inv-has-inverse H (f x))))
            ( ap f (pr2 (pr2 H) x))
            ( (ap (f ∘ (map-inv-has-inverse H ∘ f)) (pr2 (pr2 H) x)))
            ( pr1 (pr2 H) (f x))
            ( ( ap-comp f (map-inv-has-inverse H ∘ f) (pr2 (pr2 H) x)) ∙
              ( inv
                ( ap (ap f) (coh-is-coherently-invertible-id (pr2 (pr2 H)) x))))
            ( nat-htpy (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  abstract
    is-coherently-invertible-has-inverse :
      (H : has-inverse f) → is-coherently-invertible f
    pr1 (is-coherently-invertible-has-inverse H) = map-inv-has-inverse H
    pr1 (pr2 (is-coherently-invertible-has-inverse H)) =
      is-section-map-inv-has-inverse H
    pr1 (pr2 (pr2 (is-coherently-invertible-has-inverse H))) =
      is-retraction-map-inv-has-inverse H
    pr2 (pr2 (pr2 (is-coherently-invertible-has-inverse H))) =
      coherence-map-inv-has-inverse H
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
