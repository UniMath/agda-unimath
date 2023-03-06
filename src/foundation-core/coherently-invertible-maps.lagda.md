# Coherently invertible maps

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.coherently-invertible-maps where
open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
open import foundation.commuting-squares-of-identifications
```
</details>

## Idea

An inverse for a map `f : A → B` is a map `g : B → A` equipped with homotopies `
(f ∘ g) ~ id` and `(g ∘ f) ~ id`. Such data, however is structure on the map `f`, and not a property. Therefore we include an coherence condition for the homotopies of an inverse. Coherently invertible map `f : A → B` is a map equipped with a two-sided inverse and this additional coherence law. They are also called half-adjoint equivalences.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-inverse : (A → B) → UU (l1 ⊔ l2)
  has-inverse f = Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

  is-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-coherently-invertible f =
    Σ ( B → A)
      ( λ g → Σ ((f ∘ g) ~ id)
        ( λ G → Σ ((g ∘ f) ~ id)
          (λ H → coherence-is-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  inv-is-coherently-invertible : is-coherently-invertible f → B → A
  inv-is-coherently-invertible = pr1

  issec-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
  issec-inv-is-coherently-invertible H = pr1 (pr2 H)

  isretr-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
  isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

  coh-inv-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-coherently-invertible f
      ( inv-is-coherently-invertible H)
      ( issec-inv-is-coherently-invertible H)
      ( isretr-inv-is-coherently-invertible H)
  coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))
```

## Properties

### Invertible maps are coherenctly invertible

#### Lemma: A coherence for homotopies to an identity map

```agda
coh-is-coherently-invertible-id :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ (λ x → x)) →
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

  inv-has-inverse : has-inverse f → B → A
  inv-has-inverse H = pr1 H

  abstract
    issec-inv-has-inverse : (H : has-inverse f) → (f ∘ inv-has-inverse H) ~ id
    issec-inv-has-inverse H y =
      ( inv (pr1 (pr2 H) (f (inv-has-inverse H y)))) ∙
      ( ap f (pr2 (pr2 H) (inv-has-inverse H y)) ∙ (pr1 (pr2 H) y))

    isretr-inv-has-inverse : (H : has-inverse f) → (inv-has-inverse H ∘ f) ~ id
    isretr-inv-has-inverse H = pr2 (pr2 H)

    coherence-inv-has-inverse :
      (H : has-inverse f) →
      (issec-inv-has-inverse H ·r f) ~ (f ·l isretr-inv-has-inverse H)
    coherence-inv-has-inverse H x =
      inv
        ( inv-con
          ( pr1 (pr2 H) (f (inv-has-inverse H (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( ( ap f (pr2 (pr2 H) (inv-has-inverse H (f x)))) ∙
            ( pr1 (pr2 H) (f x)))
          ( coherence-square-identifications-top-paste
            ( pr1 (pr2 H) (f (inv-has-inverse H (f x))))
            ( ap f (pr2 (pr2 H) x))
            ( (ap (f ∘ (inv-has-inverse H ∘ f)) (pr2 (pr2 H) x)))
            ( pr1 (pr2 H) (f x))
            ( ( ap-comp f (inv-has-inverse H ∘ f) (pr2 (pr2 H) x)) ∙
              ( inv
                ( ap (ap f) (coh-is-coherently-invertible-id (pr2 (pr2 H)) x))))
            ( nat-htpy (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  abstract
    is-coherently-invertible-has-inverse :
      (H : has-inverse f) → is-coherently-invertible f
    pr1 (is-coherently-invertible-has-inverse H) = inv-has-inverse H
    pr1 (pr2 (is-coherently-invertible-has-inverse H)) = issec-inv-has-inverse H
    pr1 (pr2 (pr2 (is-coherently-invertible-has-inverse H))) =
      isretr-inv-has-inverse H
    pr2 (pr2 (pr2 (is-coherently-invertible-has-inverse H))) =
      coherence-inv-has-inverse H
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
