# Isomorphisms of sets

```agda
module foundation.isomorphisms-of-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

Since equality of elements in a set is a proposition, isomorphisms of sets are
equivalent to equivalences of sets

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  is-iso-Set : (f : type-hom-Set A B) → UU (l1 ⊔ l2)
  is-iso-Set f = Σ (type-hom-Set B A) (λ g → ((f ∘ g) ＝ id) × ((g ∘ f) ＝ id))

  iso-Set : UU (l1 ⊔ l2)
  iso-Set = Σ (type-hom-Set A B) is-iso-Set

  map-iso-Set : iso-Set → type-Set A → type-Set B
  map-iso-Set = pr1

  is-iso-map-iso-Set : (f : iso-Set) → is-iso-Set (map-iso-Set f)
  is-iso-map-iso-Set = pr2

  is-proof-irrelevant-is-iso-Set :
    (f : type-hom-Set A B) → is-proof-irrelevant (is-iso-Set f)
  pr1 (is-proof-irrelevant-is-iso-Set f H) = H
  pr2
    ( is-proof-irrelevant-is-iso-Set f
      ( pair g (pair p q)))
      ( pair g' (pair p' q')) =
    eq-type-subtype
      ( λ h →
        prod-Prop
          ( Id-Prop (hom-Set B B) (f ∘ h) id)
          ( Id-Prop (hom-Set A A) (h ∘ f) id))
      ( ( ap (λ h → g ∘ h) (inv p')) ∙
        ( ap (λ h → h ∘ g') q))

  is-prop-is-iso-Set : (f : type-hom-Set A B) → is-prop (is-iso-Set f)
  is-prop-is-iso-Set f =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-is-iso-Set f)

  is-iso-is-equiv-Set : {f : type-hom-Set A B} → is-equiv f → is-iso-Set f
  pr1 (is-iso-is-equiv-Set H) = map-inv-is-equiv H
  pr1 (pr2 (is-iso-is-equiv-Set H)) = eq-htpy (is-section-map-inv-is-equiv H)
  pr2 (pr2 (is-iso-is-equiv-Set H)) = eq-htpy (is-retraction-map-inv-is-equiv H)

  is-equiv-is-iso-Set : {f : type-hom-Set A B} → is-iso-Set f → is-equiv f
  is-equiv-is-iso-Set H =
    is-equiv-has-inverse
      ( pr1 H)
      ( htpy-eq (pr1 (pr2 H)))
      ( htpy-eq (pr2 (pr2 H)))

  iso-equiv-Set : type-equiv-Set A B → iso-Set
  pr1 (iso-equiv-Set e) = map-equiv e
  pr2 (iso-equiv-Set e) = is-iso-is-equiv-Set (is-equiv-map-equiv e)

  equiv-iso-Set : iso-Set → type-equiv-Set A B
  pr1 (equiv-iso-Set f) = map-iso-Set f
  pr2 (equiv-iso-Set f) = is-equiv-is-iso-Set (is-iso-map-iso-Set f)

  equiv-iso-equiv-Set : type-equiv-Set A B ≃ iso-Set
  equiv-iso-equiv-Set =
    equiv-type-subtype
      ( is-property-is-equiv)
      ( is-prop-is-iso-Set)
      ( λ f → is-iso-is-equiv-Set)
      ( λ f → is-equiv-is-iso-Set)
```
