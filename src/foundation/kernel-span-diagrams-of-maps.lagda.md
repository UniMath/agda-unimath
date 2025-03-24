# Kernel span diagrams of maps

```agda
open import foundation.function-extensionality-axiom

module foundation.kernel-span-diagrams-of-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.span-diagrams funext
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Consider a map `f : A → B`. The
{{#concept "kernel span diagram" Disambiguation="map" Agda=kernel-span-diagram}}
of `f` is the [span diagram](foundation.span-diagrams.md)

```text
      pr1                           pr1 ∘ pr2
  A <----- Σ (x y : A), f x ＝ f y -----------> A.
```

We call this the kernel span diagram, since the pair `(pr1 , pr1 ∘ pr2)` is
often called the kernel pair of a map.

## Definitions

### Kernel span diagrams of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  spanning-type-kernel-span : UU (l1 ⊔ l2)
  spanning-type-kernel-span =
    Σ A (λ x → Σ A (λ y → f x ＝ f y))

  left-map-kernel-span :
    spanning-type-kernel-span → A
  left-map-kernel-span = pr1

  right-map-kernel-span :
    spanning-type-kernel-span → A
  right-map-kernel-span = pr1 ∘ pr2

  kernel-span : span (l1 ⊔ l2) A A
  pr1 kernel-span =
    spanning-type-kernel-span
  pr1 (pr2 kernel-span) =
    left-map-kernel-span
  pr2 (pr2 kernel-span) =
    right-map-kernel-span

  domain-kernel-span-diagram : UU l1
  domain-kernel-span-diagram = A

  codomain-kernel-span-diagram : UU l1
  codomain-kernel-span-diagram = A

  kernel-span-diagram : span-diagram l1 l1 (l1 ⊔ l2)
  pr1 kernel-span-diagram = domain-kernel-span-diagram
  pr1 (pr2 kernel-span-diagram) = codomain-kernel-span-diagram
  pr2 (pr2 kernel-span-diagram) = kernel-span
```
