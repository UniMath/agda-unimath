---
title: Split surjective maps
---

```agda
module foundation.split-surjective-maps where

open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universe-levels
```

## Idea

A map `f : A → B` is split surjective if we can construct for every `b : B` an element `a : A` equipped with an identification `Id (f a) b`.

## Warning

Note that split-surjectiveness is the Curry-Howard interpretation of surjectiveness. However, this is not a property, and the split surjective maps don't fit in a factorization system along with the injective maps. 

## Definition

### Split surjective maps

```agda
is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-split-surjective {A = A} {B} f = (b : B) → Σ A (λ a → f a ＝ b)
```

## Properties

### Split surjections are maps equipped with a section

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  sec-is-split-surjective : is-split-surjective f → sec f
  pr1 (sec-is-split-surjective s) = pr1 ∘ s
  pr2 (sec-is-split-surjective s) = pr2 ∘ s

  is-split-surjective-sec : sec f → is-split-surjective f
  pr1 (is-split-surjective-sec s b) = pr1 s b
  pr2 (is-split-surjective-sec s b) = pr2 s b

  is-equiv-sec-is-split-surjective : is-equiv sec-is-split-surjective
  pr1 (pr1 is-equiv-sec-is-split-surjective) = is-split-surjective-sec
  pr2 (pr1 is-equiv-sec-is-split-surjective) = refl-htpy
  pr1 (pr2 is-equiv-sec-is-split-surjective) = is-split-surjective-sec
  pr2 (pr2 is-equiv-sec-is-split-surjective) = refl-htpy

  is-equiv-is-split-surjective-sec : is-equiv is-split-surjective-sec
  pr1 (pr1 is-equiv-is-split-surjective-sec) = sec-is-split-surjective
  pr2 (pr1 is-equiv-is-split-surjective-sec) = refl-htpy
  pr1 (pr2 is-equiv-is-split-surjective-sec) = sec-is-split-surjective
  pr2 (pr2 is-equiv-is-split-surjective-sec) = refl-htpy

  equiv-sec-is-split-surjective : is-split-surjective f ≃ sec f
  pr1 equiv-sec-is-split-surjective = sec-is-split-surjective
  pr2 equiv-sec-is-split-surjective = is-equiv-sec-is-split-surjective

  equiv-is-split-surjective-sec : sec f ≃ is-split-surjective f
  pr1 equiv-is-split-surjective-sec = is-split-surjective-sec
  pr2 equiv-is-split-surjective-sec = is-equiv-is-split-surjective-sec
```

### A map is an equivalence if and only if it is injective and split surjective

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  retr-is-split-surjective-is-injective :
    is-injective f → is-split-surjective f → retr f
  pr1 (retr-is-split-surjective-is-injective l s) = pr1 ∘ s
  pr2 (retr-is-split-surjective-is-injective l s) = l ∘ (pr2 ∘ (s ∘ f))

  is-equiv-is-split-surjective-is-injective :
    is-injective f → is-split-surjective f → is-equiv f
  pr1 (is-equiv-is-split-surjective-is-injective l s) =
    sec-is-split-surjective f s
  pr2 (is-equiv-is-split-surjective-is-injective l s) =
    retr-is-split-surjective-is-injective l s

  is-split-surjective-is-equiv : is-equiv f → is-split-surjective f
  is-split-surjective-is-equiv = is-split-surjective-sec f ∘ pr1
```
 