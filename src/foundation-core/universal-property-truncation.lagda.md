# The universal property of truncations

```agda
module foundation-core.universal-property-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sections
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

We say that a map `f : A → B` into a `k`-truncated type `B` is a
**`k`-truncation** of `A` -- or that it **satisfies the universal property of
the `k`-truncation** of `A` -- if any map `g : A → C` into a `k`-truncated type
`C` extends uniquely along `f` to a map `B → C`.

## Definition

### The condition on a map to be a truncation

```agda
precomp-Trunc :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : Truncated-Type l3 k) →
  (B → type-Truncated-Type C) → (A → type-Truncated-Type C)
precomp-Trunc f C = precomp f (type-Truncated-Type C)

is-truncation :
  (l : Level) {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) → (A → type-Truncated-Type B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
is-truncation l {k = k} B f =
  (C : Truncated-Type l k) → is-equiv (precomp-Trunc f C)

equiv-is-truncation :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  (H : {l : Level} → is-truncation l B f) →
  (C : Truncated-Type l3 k) →
  (type-Truncated-Type B → type-Truncated-Type C) ≃ (A → type-Truncated-Type C)
pr1 (equiv-is-truncation B f H C) = precomp-Trunc f C
pr2 (equiv-is-truncation B f H C) = H C
```

### The universal property of truncations

```agda
universal-property-truncation :
  (l : Level) {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
  UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-truncation l {k = k} {A} B f =
  (C : Truncated-Type l k) (g : A → type-Truncated-Type C) →
  is-contr (Σ (type-hom-Truncated-Type k B C) (λ h → (h ∘ f) ~ g))
```

### The dependent universal property of truncations

```agda
precomp-Π-Truncated-Type :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  (C : B → Truncated-Type l3 k) →
  ((b : B) → type-Truncated-Type (C b)) →
  ((a : A) → type-Truncated-Type (C (f a)))
precomp-Π-Truncated-Type f C h a = h (f a)

dependent-universal-property-truncation :
  {l1 l2 : Level} (l : Level) {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B) → UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-truncation l {k} B f =
  (X : type-Truncated-Type B → Truncated-Type l k) →
  is-equiv (precomp-Π-Truncated-Type f X)
```

## Properties

### Equivalences into `k`-truncated types are truncations

```agda
abstract
  is-truncation-id :
    {l1 : Level} {k : 𝕋} {A : UU l1} (H : is-trunc k A) →
    {l : Level} → is-truncation l (A , H) id
  is-truncation-id H B =
    is-equiv-precomp-is-equiv id is-equiv-id (type-Truncated-Type B)

abstract
  is-truncation-equiv :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
    (e : A ≃ type-Truncated-Type B) →
    {l : Level} → is-truncation l B (map-equiv e)
  is-truncation-equiv B e C =
    is-equiv-precomp-is-equiv
      ( map-equiv e)
      ( is-equiv-map-equiv e)
      ( type-Truncated-Type C)
```

### A map into a truncated type is a truncation if and only if it satisfies the universal property of the truncation

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  where

  abstract
    is-truncation-universal-property-truncation :
      ({l : Level} → universal-property-truncation l B f) →
      ({l : Level} → is-truncation l B f)
    is-truncation-universal-property-truncation H C =
      is-equiv-is-contr-map
        ( λ g →
          is-contr-equiv
            ( Σ (type-hom-Truncated-Type k B C) (λ h → (h ∘ f) ~ g))
            ( equiv-tot (λ h → equiv-funext))
            ( H C g))

  abstract
    universal-property-truncation-is-truncation :
      ({l : Level} → is-truncation l B f) →
      ({l : Level} → universal-property-truncation l B f)
    universal-property-truncation-is-truncation H C g =
      is-contr-equiv'
        ( Σ (type-hom-Truncated-Type k B C) (λ h → (h ∘ f) ＝ g))
        ( equiv-tot (λ h → equiv-funext))
        ( is-contr-map-is-equiv (H C) g)

  map-is-truncation :
    ({l : Level} → is-truncation l B f) →
    ({l : Level} (C : Truncated-Type l k) (g : A → type-Truncated-Type C) →
    type-hom-Truncated-Type k B C)
  map-is-truncation H C g =
    pr1 (center (universal-property-truncation-is-truncation H C g))

  triangle-is-truncation :
    (H : {l : Level} → is-truncation l B f) →
    {l : Level} (C : Truncated-Type l k) (g : A → type-Truncated-Type C) →
    (map-is-truncation H C g ∘ f) ~ g
  triangle-is-truncation H C g =
    pr2 (center (universal-property-truncation-is-truncation H C g))
```

### A map into a truncated type is a truncation if and only if it satisfies the dependent universal property of the truncation

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k)
  (f : A → type-Truncated-Type B)
  where

  abstract
    dependent-universal-property-truncation-is-truncation :
      ({l : Level} → is-truncation l B f) →
      {l : Level} → dependent-universal-property-truncation l B f
    dependent-universal-property-truncation-is-truncation H X =
      is-fiberwise-equiv-is-equiv-map-Σ
        ( λ (h : A → type-Truncated-Type B) →
          (a : A) → type-Truncated-Type (X (h a)))
        ( λ (g : type-Truncated-Type B → type-Truncated-Type B) → g ∘ f)
        ( λ g (s : (b : type-Truncated-Type B) →
          type-Truncated-Type (X (g b))) (a : A) → s (f a))
        ( H B)
        ( is-equiv-equiv
          ( inv-distributive-Π-Σ)
          ( inv-distributive-Π-Σ)
          ( ind-Σ (λ g s → refl))
          ( H (Σ-Truncated-Type B X)))
        ( id)

  abstract
    is-truncation-dependent-universal-property-truncation :
      ({l : Level} → dependent-universal-property-truncation l B f) →
      {l : Level} → is-truncation l B f
    is-truncation-dependent-universal-property-truncation H X =
      H (λ b → X)

  section-is-truncation :
    ({l : Level} → is-truncation l B f) →
    {l3 : Level} (C : Truncated-Type l3 k)
    (h : A → type-Truncated-Type C) (g : type-hom-Truncated-Type k C B) →
    f ~ (g ∘ h) → section g
  section-is-truncation H C h g K =
    map-distributive-Π-Σ
      ( map-inv-is-equiv
        ( dependent-universal-property-truncation-is-truncation H
          ( fiber-Truncated-Type C B g))
        ( λ a → h a , inv (K a)))
```
