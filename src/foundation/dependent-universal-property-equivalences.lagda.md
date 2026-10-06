# The dependent universal property of equivalences

```agda
module foundation.dependent-universal-property-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.path-split-maps
open import foundation-core.precomposition-dependent-functions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The **dependent universal property of equivalences** states that, for a given
map `f : A → B`, the
[precomposition of dependent functions](foundation-core.precomposition-dependent-functions.md)
by `f`

```text
  - ∘ f : ((b : B) → C b) → ((a : A) → C (f a))
```

is an [equivalence](foundation-core.equivalences.md) for every type family `C`
over `B`. A map `f : A → B` satisfies the dependent universal property of
equivalences if and only if it is an equivalence.

## Definitions

### The dependent universal property of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  dependent-universal-property-equiv : UUω
  dependent-universal-property-equiv =
    {l : Level} (C : B → UU l) → is-equiv (precomp-Π f C)
```

## Properties

### If `f` is coherently invertible, then `f` satisfies the dependent universal property of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-precomp-Π-is-coherently-invertible :
      is-coherently-invertible f → dependent-universal-property-equiv f
    is-equiv-precomp-Π-is-coherently-invertible
      ( g , is-section-g , is-retraction-g , coh) C =
      is-equiv-is-invertible
        ( λ s y → tr C (is-section-g y) (s (g y)))
        ( λ s →
          eq-htpy
            ( λ x →
              ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
              ( substitution-law-tr C f (is-retraction-g x)) ∙
              ( apd s (is-retraction-g x))))
        ( λ s → eq-htpy (λ y → apd s (is-section-g y)))
```

### If `f` is an equivalence, then `f` satisfies the dependent universal property of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  abstract
    is-equiv-precomp-Π-is-equiv :
      dependent-universal-property-equiv f
    is-equiv-precomp-Π-is-equiv =
      is-equiv-precomp-Π-is-coherently-invertible f
        ( is-coherently-invertible-is-path-split f
          ( is-path-split-is-equiv f H))

  map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) → ((a : A) → C (f a)) → ((b : B) → C b)
  map-inv-is-equiv-precomp-Π-is-equiv C =
    map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C)

  is-section-map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) →
    (h : (a : A) → C (f a)) →
    precomp-Π f C (map-inv-is-equiv-precomp-Π-is-equiv C h) ~ h
  is-section-map-inv-is-equiv-precomp-Π-is-equiv C h =
    htpy-eq (is-section-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C) h)

  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv :
    {l3 : Level} (C : B → UU l3) →
    (g : (b : B) → C b) →
    map-inv-is-equiv-precomp-Π-is-equiv C (precomp-Π f C g) ~ g
  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv C g =
    htpy-eq (is-retraction-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv C) g)

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) = is-equiv-precomp-Π-is-equiv (is-equiv-map-equiv e) C
```
