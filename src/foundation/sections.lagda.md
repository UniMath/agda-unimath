# Sections

<details><summary>Imports</summary>
```agda
module foundation.sections where
open import foundation-core.sections public
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels
open import foundation.function-extensionality
open import foundation.injective-maps
open import foundation.structure-identity-principle
open import foundation.type-theoretic-principle-of-choice
```
</details>

## Idea

Any dependent function induces a section of the projection map

## Properties

### Sections of the projection map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  map-section : ((x : A) → B x) → (A → Σ A B)
  pr1 (map-section b a) = a
  pr2 (map-section b a) = b a

  htpy-map-section :
    (b : (x : A) → B x) → (pr1 ∘ map-section b) ~ id
  htpy-map-section b a = refl

  sec-dependent-function : ((x : A) → B x) → sec (pr1 {B = B})
  pr1 (sec-dependent-function b) = map-section b
  pr2 (sec-dependent-function b) = htpy-map-section b
```

### Any section of a type family is an equivalence if and only if each type in the family is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-equiv-map-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → is-equiv (map-section b)
  is-equiv-map-section b C =
    is-equiv-right-factor-htpy
      ( id)
      ( pr1)
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-pr1-is-contr C)
      ( is-equiv-id)

  equiv-section :
    (b : (x : A) → B x) → ((x : A) → is-contr (B x)) → A ≃ Σ A B
  equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

  is-contr-fam-is-equiv-map-section :
    (b : (x : A) → B x) → is-equiv (map-section b) → ((x : A) → is-contr (B x))
  is-contr-fam-is-equiv-map-section b H =
    is-contr-is-equiv-pr1
      ( is-equiv-left-factor-htpy id pr1
        ( map-section b)
        ( htpy-map-section b)
        ( is-equiv-id)
        ( H))
```

```agda
equiv-total-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  Σ (Σ A B) (fib (map-section b)) ≃ A
equiv-total-fib-map-section b = equiv-total-fib (map-section b)
```

### Any section of a type family is an injective map

```agda
is-injective-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section b)
is-injective-map-section b = ap pr1
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-sec-pr1 : sec (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-sec-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → y ＝ x))
          ( inv-distributive-Π-Σ)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( distributive-Π-Σ)
      ( λ s → id-equiv))
```

### Extensionality of sections

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  htpy-sec : (s t : sec f) → UU (l1 ⊔ l2)
  htpy-sec s t = Σ (pr1 s ~ pr1 t) (λ H → pr2 s ~ ((f ·l H) ∙h pr2 t))

  extensionality-sec : (s t : sec f) → (s ＝ t) ≃ htpy-sec s t
  extensionality-sec (pair s H) =
    extensionality-Σ
      ( λ {s'} H' K → H ~ ((f ·l K) ∙h H'))
      ( refl-htpy)
      ( refl-htpy)
      ( λ s' → equiv-funext)
      ( λ H' → equiv-funext)

  eq-htpy-sec :
    (s t : sec f)
    (H : (pr1 s) ~ (pr1 t)) (K : (pr2 s) ~ ((f ·l H) ∙h (pr2 t))) → s ＝ t
  eq-htpy-sec s t H K =
    map-inv-equiv (extensionality-sec s t) (pair H K)
```

### If the right factor of a composite has a section, then the type of sections of the left factor is a retract of the type of sections of the composite.

```agda
isretr-section-comp-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (sec-h : sec h) →
  ((section-left-factor-htpy f g h H) ∘ (section-comp-htpy f g h H sec-h)) ~ id
isretr-section-comp-htpy f g h H (pair k K) (pair l L) =
  eq-htpy-sec
    ( ( section-left-factor-htpy f g h H ∘
        section-comp-htpy f g h H (pair k K))
      ( pair l L))
    ( pair l L)
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

sec-left-factor-retract-of-sec-composition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → (sec g) retract-of (sec f)
pr1 (sec-left-factor-retract-of-sec-composition f g h H sec-h) =
  section-comp-htpy f g h H sec-h
pr1 (pr2 (sec-left-factor-retract-of-sec-composition f g h H sec-h)) =
  section-left-factor-htpy f g h H
pr2 (pr2 (sec-left-factor-retract-of-sec-composition f g h H sec-h)) =
  isretr-section-comp-htpy f g h H sec-h
```
