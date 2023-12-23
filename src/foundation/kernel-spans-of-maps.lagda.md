# Kernel spans of maps

```agda
module foundation.kernel-spans-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Consider a map `f : A → B`. The {{#concept "kernel span" Disambiguation="map"}} of `f` is the [span](foundation.spans.md)

```text
      pr1                           pr1 ∘ pr2
  A <----- Σ (x y : A), f x ＝ f y -----------> A.
```

## Definitions

### Kernel spans of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  spanning-type-kernel-span-fixed-domain-codomain : UU (l1 ⊔ l2)
  spanning-type-kernel-span-fixed-domain-codomain =
    Σ A (λ x → Σ A (λ y → f x ＝ f y))

  left-map-kernel-span-fixed-domain-codomain :
    spanning-type-kernel-span-fixed-domain-codomain → A
  left-map-kernel-span-fixed-domain-codomain = pr1

  right-map-kernel-span-fixed-domain-codomain :
    spanning-type-kernel-span-fixed-domain-codomain → A
  right-map-kernel-span-fixed-domain-codomain = pr1 ∘ pr2

  kernel-span-fixed-domain-codomain : span-fixed-domain-codomain (l1 ⊔ l2) A A
  pr1 kernel-span-fixed-domain-codomain =
    spanning-type-kernel-span-fixed-domain-codomain
  pr1 (pr2 kernel-span-fixed-domain-codomain) =
    left-map-kernel-span-fixed-domain-codomain
  pr2 (pr2 kernel-span-fixed-domain-codomain) =
    right-map-kernel-span-fixed-domain-codomain

  domain-kernel-span : UU l1
  domain-kernel-span = A

  codomain-kernel-span : UU l1
  codomain-kernel-span = A

  kernel-span : span l1 l1 (l1 ⊔ l2)
  pr1 kernel-span = domain-kernel-span
  pr1 (pr2 kernel-span) = codomain-kernel-span
  pr2 (pr2 kernel-span) = kernel-span-fixed-domain-codomain
```
