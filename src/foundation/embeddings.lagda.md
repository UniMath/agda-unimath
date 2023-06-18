# Embeddings

```agda
module foundation.embeddings where

open import foundation-core.embeddings public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.sections
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being an embedding is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-emb : (f : A → B) → is-prop (is-emb f)
  is-prop-is-emb f =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-equiv (ap f)))

  is-emb-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-emb-Prop f) = is-emb f
  pr2 (is-emb-Prop f) = is-prop-is-emb f
```

### Embeddings are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where

  abstract
    is-emb-htpy : is-emb g → is-emb f
    is-emb-htpy is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( ap g)
        ( concat' (f x) (H y))
        ( ap f)
        ( concat (H x) (g y))
        ( nat-htpy H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where

  abstract
    is-emb-htpy' : is-emb f → is-emb g
    is-emb-htpy' is-emb-f =
      is-emb-htpy g f (inv-htpy H) is-emb-f
```

### Any map between propositions is an embedding

```agda
is-emb-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop A → is-prop B → is-emb f
is-emb-is-prop H K =
  is-emb-is-prop-map (is-trunc-map-is-trunc-domain-codomain neg-one-𝕋 H K)
```

### Embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-comp :
    (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp g h is-emb-g is-emb-h x y =
    is-equiv-comp-htpy (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y))

  abstract
    is-emb-comp-htpy :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb h → is-emb f
    is-emb-comp-htpy f g h H is-emb-g is-emb-h =
      is-emb-htpy f (g ∘ h) H (is-emb-comp g h is-emb-g is-emb-h)

  comp-emb :
    (B ↪ C) → (A ↪ B) → (A ↪ C)
  comp-emb (pair g H) (pair f K) = pair (g ∘ f) (is-emb-comp g f H K)
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-right-factor :
    (g : B → C) (h : A → B) →
    is-emb g → is-emb (g ∘ h) → is-emb h
  is-emb-right-factor g h is-emb-g is-emb-gh x y =
    is-equiv-right-factor-htpy
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-g (h x) (h y))
      ( is-emb-gh x y)

  abstract
    is-emb-right-factor-htpy :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) →
      is-emb g → is-emb f → is-emb h
    is-emb-right-factor-htpy f g h H is-emb-g is-emb-f x y =
      is-equiv-right-factor-htpy
        ( ap (g ∘ h))
        ( ap g)
        ( ap h)
        ( ap-comp g h)
        ( is-emb-g (h x) (h y))
        ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-comp-htpy f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb f → is-emb g
    is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
      is-emb-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( is-section-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-emb-f)
```

### The map on total spaces induced by a family of embeddings is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-emb-tot :
    {f : (x : A) → B x → C x} → ((x : A) → is-emb (f x)) → is-emb (tot f)
  is-emb-tot H =
    is-emb-is-prop-map (is-prop-map-tot (λ x → is-prop-map-is-emb (H x)))

  tot-emb : ((x : A) → B x ↪ C x) → Σ A B ↪ Σ A C
  pr1 (tot-emb f) = tot (λ x → map-emb (f x))
  pr2 (tot-emb f) = is-emb-tot (λ x → is-emb-map-emb (f x))
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) → is-emb f → is-emb (map-Σ-map-base f C)
    is-emb-map-Σ-map-base C H =
      is-emb-is-prop-map (is-prop-map-map-Σ-map-base C (is-prop-map-is-emb H))

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = map-Σ-map-base (map-emb f) C
  pr2 (emb-Σ-emb-base f C) =
    is-emb-map-Σ-map-base C (is-emb-map-emb f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-emb-map-Σ :
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
  is-emb-map-Σ D H K =
    is-emb-is-prop-map
      ( is-prop-map-map-Σ D
        ( is-prop-map-is-emb H)
        ( λ x → is-prop-map-is-emb (K x)))

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = map-Σ D (map-emb f) (λ x → map-emb (g x))
  pr2 (emb-Σ D f g) =
    is-emb-map-Σ D (is-emb-map-emb f) (λ x → is-emb-map-emb (g x))
```

### The product of two embeddings is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  emb-prod : (A ↪ C) → (B ↪ D) → ((A × B) ↪ (C × D))
  emb-prod f g = emb-Σ (λ _ → D) f (λ _ → g)

  is-emb-map-prod :
    (f : A → C) (g : B → D) → is-emb f → is-emb g → (is-emb (map-prod f g))
  is-emb-map-prod f g is-emb-f is-emb-g =
    is-emb-map-emb (emb-prod (f , is-emb-f) (g , is-emb-g))
```

### If the action on identifications has a section, then `f` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-section-ap :
      ((x y : A) → section (ap f {x = x} {y = y})) → is-emb f
    is-emb-section-ap section-ap-f x y =
      fundamental-theorem-id-section x (λ y → ap f {y = y}) (section-ap-f x) y
```

### If there is an equivalence `(f x = f y) ≃ (x = y)` that sends `refl` to `refl`, then f is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-equiv-refl-to-refl :
      (e : (x y : A) → (f x ＝ f y) ≃ (x ＝ y)) →
      ((x : A) → map-equiv (e x x) refl ＝ refl) →
      is-emb f
    is-emb-equiv-refl-to-refl e p x y =
      is-equiv-htpy-equiv
        (inv-equiv (e x y))
        λ { refl →
              inv (is-retraction-map-inv-equiv (e x x) refl) ∙
              ap (map-equiv (inv-equiv (e x x))) (p x)}
```

### Embeddings are closed under pullback

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-emb-vertical-map-cone-is-pullback :
      is-pullback f g c → is-emb g → is-emb (vertical-map-cone f g c)
    is-emb-vertical-map-cone-is-pullback pb is-emb-g =
      is-emb-is-prop-map
        ( is-trunc-is-pullback neg-one-𝕋 f g c pb (is-prop-map-is-emb is-emb-g))

  abstract
    is-emb-horizontal-map-cone-is-pullback :
      is-pullback f g c → is-emb f → is-emb (horizontal-map-cone f g c)
    is-emb-horizontal-map-cone-is-pullback pb is-emb-f =
      is-emb-is-prop-map
        ( is-trunc-is-pullback' neg-one-𝕋 f g c pb
          ( is-prop-map-is-emb is-emb-f))
```

### In a commuting square of which the sides are embeddings, the top map is an embedding if and only if the bottom map is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb bottom → is-emb top
  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps K L M =
    is-emb-right-factor
      ( right)
      ( top)
      ( is-emb-is-equiv L)
      ( is-emb-htpy'
        ( bottom ∘ left)
        ( right ∘ top)
        ( H)
        ( is-emb-comp bottom left M (is-emb-is-equiv K)))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb top → is-emb bottom
  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps K L M =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps
      ( bottom)
      ( map-inv-is-equiv K)
      ( map-inv-is-equiv L)
      ( top)
      ( coherence-square-inv-vertical
        ( top)
        ( left , K)
        ( right , L)
        ( bottom)
        ( H))
      ( is-equiv-map-inv-is-equiv K)
      ( is-equiv-map-inv-is-equiv L)
      ( M)
```
