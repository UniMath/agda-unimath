# The Universal Property of Fibers of Maps

```agda
module foundation.universal-property-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-function-types
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

A map `f : A → B` induces a type family `fiber f : B → UU`. By precomposing with
`f`, we have another type family `(fiber f) ∘ f : A → UU`. This latter type
family always has a section given by
`λ a → (a , refl) : (a : A) → fiber f (f a)`.

We can uniquely characterize the family of fibers `fiber f : B → UU` as the
initial type family equipped with such a section. Explicitly, `fiber f : B → UU`
is initial amoung type families `P : B → UU` equipped with sections
`(a : A) → P (f a)`. This can be packaged into an equivalence between fiberwise
maps from `fiber f` to `P` and sections of `B ∘ f`:

```text
((b : B) → fiber f b → P b) ≃ ((a : A) → P (f a))
```

This universal property is especially useful when `A` itself enjoys a mapping
out universal property. This lets us characterize the sections
`(a : A) → B (f a)`. And, in the case that `f` was defined using the mapping out
property of `A`, we may obtain an even nicer characterization.

For example, if we take `A` to be `unit` and the map `f : unit → B` to be
defined by a point `b₀ : B` and the universal property of `unit`, we have

```text
((b : B) → fiber f b → P b) ≃ ((t : unit) → P (f t)) ≃ ((t : unit) → P b₀) ≃ P b₀
```

which essentialy tells us `fiber f : B → UU` has the same universal property as
`Id b₀ : B → UU`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  ev-fiber :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) {l4 : Level}
    (P : B → UU l4) → ((b : B) → F b → P b) → (a : A) → P (f a)
  ev-fiber f F δ P h a = h (f a) (δ a)

  universal-property-fiber :
    (l : Level) (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
  universal-property-fiber l f F δ = (P : B → UU l) → is-equiv (ev-fiber f F δ P)

  fiberwise-map-universal-property-fiber :
    (f : A → B) (F : B → UU l3) (δ : (a : A) → F (f a)) {l4 : Level} →
    ({l : Level} → universal-property-fiber l f F δ) →
    {l4 : Level} (P : B → UU l4) → ((a : A) → P (f a)) →
    (b : B) → F b → P b
  fiberwise-map-universal-property-fiber f F δ u P γ =
    map-inv-is-equiv (u P) γ
```

## Properties

### The 3-for-2 Property for fibers of maps {- THIS REQUIRES INFRASTRUCTURE FOR COMPOSING DEPENDENT FUNCTIONS -}

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) {F : B → UU l3}
  (δ : (a : A) → F (f a)) {P : B → UU l4} (γ : (a : A) → P (f a))
  (h : (b : B) → F b → P b) (H : (ev-fiber f F δ P h) ~ γ)
  where

  triangle-ev-fiber :
    {l5 : Level} (C : B → UU l5) →
    (ev-fiber f P γ C) ~ ((ev-fiber f F δ C ) ∘ (λ (k : (b : B) → P b → C b) b t → k b (h b t)))
  triangle-ev-fiber C = {!!}  
```

### Fibers are uniquely unique

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (F : B → UU l3)
  (δ : (a : A) → F (f a)) (u : {l : Level} → universal-property-fiber l f F δ)
  (P : B → UU l4) (γ : (a : A) → P (f a))
  where

  uniqueness-fiberwise-map-universal-property-fiber :
    is-contr (Σ ((b : B) → F b → P b) (λ h → (ev-fiber f F δ P h) ~ γ))
  uniqueness-fiberwise-map-universal-property-fiber =
    is-contr-equiv
      ( fiber (ev-fiber f F δ P) γ)
      ( equiv-tot
        ( λ h → equiv-eq-htpy))
      (  is-contr-map-is-equiv (u P) γ)

  uniquely-unique-fiberwise-map-universal-property-fiber :
    (u' : {l : Level} → universal-property-fiber l f P γ) →
    is-contr
      ( Σ (fiberwise-equiv F P) (λ h → (ev-fiber f F δ P (fiberwise-map-fiberwise-equiv h)) ~ γ))
  uniquely-unique-fiberwise-map-universal-property-fiber u' =
    is-torsorial-Eq-subtype
      ( uniqueness-fiberwise-map-universal-property-fiber)
      ( is-property-is-fiberwise-equiv)
      ( fiberwise-map-universal-property-fiber f F δ u P γ)
      ( htpy-eq (is-section-map-inv-is-equiv (u P) γ))
      ( {!!})
```
  unique-fiber :
    ({l : Level} → universal-property-fiber l f F δ) →
    ({l : Level} → universal-property-fiber l f F' δ') → (b : B) → F b ≃ F' b
  pr1 (unique-fiber u u' b) = map-inv-is-equiv (u F') δ' b
  pr2 (unique-fiber u u' b) =
    is-equiv-is-invertible
      ( map-inv-is-equiv (u' F) δ b)
      ( {!s!})
      ( {!r!})

