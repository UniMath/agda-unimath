# Sections

```agda
module foundation.sections where

open import foundation-core.sections public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.retractions
```

</details>

## Definitions

### Sections of the projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section-family : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section-family b a) = a
  pr2 (map-section-family b a) = b a

  htpy-map-section-family :
    (b : (x : A) → B x) → (pr1 ∘ map-section-family b) ~ id
  htpy-map-section-family b a = refl

  section-dependent-function : ((x : A) → B x) → section (pr1 {B = B})
  pr1 (section-dependent-function b) = map-section-family b
  pr2 (section-dependent-function b) = htpy-map-section-family b
```

## Properties

### Extensionality of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  htpy-section : (s t : section f) → UU (l1 ⊔ l2)
  htpy-section s t = Σ (pr1 s ~ pr1 t) (λ H → pr2 s ~ ((f ·l H) ∙h pr2 t))

  extensionality-section : (s t : section f) → (s ＝ t) ≃ htpy-section s t
  extensionality-section (s , H) =
    extensionality-Σ
      ( λ {s'} H' K → H ~ ((f ·l K) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ s' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-section :
    (s t : section f)
    (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) → s ＝ t
  eq-htpy-section s t H K =
    map-inv-equiv (extensionality-section s t) (H , K)
```

### If the right factor of a composite has a section, then the type of sections of the left factor is a retract of the type of sections of the composite

```agda
is-retraction-section-comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ (g ∘ h)) (s : section h) →
  (section-left-factor-htpy f g h H ∘ section-comp-htpy f g h H s) ~ id
is-retraction-section-comp-htpy f g h H (k , K) (l , L) =
  eq-htpy-section
    ( ( section-left-factor-htpy f g h H ∘
        section-comp-htpy f g h H (k , K))
      ( l , L))
    ( l , L)
    ( K ·r l)
    ( ( inv-htpy-assoc-htpy
        ( inv-htpy (H ·r (k ∘ l)))
        ( H ·r (k ∘ l))
        ( (g ·l (K ·r l)) ∙h L)) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy (H ·r (k ∘ l))) ∙h (H ·r (k ∘ l)))
        ( refl-htpy)
        ( (g ·l (K ·r l)) ∙h L)
        ( left-inv-htpy (H ·r (k ∘ l)))))

section-left-factor-retract-of-section-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  section h → (section g) retract-of (section f)
pr1 (section-left-factor-retract-of-section-composition f g h H s) =
  section-comp-htpy f g h H s
pr1 (pr2 (section-left-factor-retract-of-section-composition f g h H s)) =
  section-left-factor-htpy f g h H

pr2 (pr2 (section-left-factor-retract-of-section-composition f g h H s)) =
  is-retraction-section-comp-htpy f g h H s
```

### The equivalence of sections of the projection map and sections of the type family

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-section-pr1 : section (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-section-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → y ＝ x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( id , refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
```

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x)
  where

  is-equiv-map-section-family :
    ((x : A) → is-contr (B x)) → is-equiv (map-section-family b)
  is-equiv-map-section-family C =
    is-equiv-right-factor-htpy
      ( id)
      ( pr1)
      ( map-section-family b)
      ( htpy-map-section-family b)
      ( is-equiv-pr1-is-contr C)
      ( is-equiv-id)

  equiv-section :
    ((x : A) → is-contr (B x)) → A ≃ Σ A B
  pr1 (equiv-section C) = map-section-family b
  pr2 (equiv-section C) = is-equiv-map-section-family C

  is-contr-fam-is-equiv-map-section-family :
    is-equiv (map-section-family b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section-family H =
    is-contr-is-equiv-pr1
      ( is-equiv-left-factor-htpy id pr1
        ( map-section-family b)
        ( htpy-map-section-family b)
        ( is-equiv-id)
        ( H))
```

### Any section of a type family is an injective map

```agda
is-injective-map-section-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section-family b)
is-injective-map-section-family b = ap pr1
```

### Transposing identifications along sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  transpose-eq-section :
    (g : B → A) (H : (f ∘ g) ~ id) {x : A} {y : B} →
    x ＝ g y → f x ＝ y
  transpose-eq-section g H refl = H _

  transpose-eq-section' :
    (g : B → A) (H : (f ∘ g) ~ id) {x : B} {y : A} →
    g x ＝ y → x ＝ f y
  transpose-eq-section' g H refl = inv (H _)
```
