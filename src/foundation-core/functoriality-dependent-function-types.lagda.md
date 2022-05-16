---
title: Functoriality of dependent function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.functoriality-dependent-function-types where

open import foundation.contractible-types
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs

open import foundation-core.contractible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels
```

## Properties

### The operation `map-Π` preserves homotopies

```agda
htpy-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  (map-Π f) ~ (map-Π f')
htpy-map-Π H h = eq-htpy (λ i → H i (h i))

htpy-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) {f f' : (i : I) → A i → B i} →
  ((i : I) → (f i) ~ (f' i)) → (map-Π' α f ~ map-Π' α f')
htpy-map-Π' α H = htpy-map-Π (λ j → H (α j))
```

### We compute the fibers of map-Π

```agda
equiv-fib-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fib (f i) (h i)) ≃ fib (map-Π f) h
equiv-fib-map-Π f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e distributive-Π-Σ
```

### Families of equivalences induce equivalences on dependent function types

```agda
abstract
  is-equiv-map-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (f : (i : I) → A i → B i) (is-equiv-f : is-fiberwise-equiv f) →
    is-equiv (map-Π f)
  is-equiv-map-Π f is-equiv-f =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv' _
          ( equiv-fib-map-Π f g)
          ( is-contr-Π (λ i → is-contr-map-is-equiv (is-equiv-f i) (g i))))

equiv-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
pr1 (equiv-map-Π e) = map-Π (λ i → map-equiv (e i))
pr2 (equiv-map-Π e) = is-equiv-map-Π _ (λ i → is-equiv-map-equiv (e i))
```
