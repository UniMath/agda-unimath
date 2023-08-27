# Invertible maps

```agda
module foundation.invertible-maps where

open import foundation-core.invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Properties

### Characterizing equality of invertible maps

#### Characterizing equality of `is-inverse`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  htpy-is-inverse : (s t : is-inverse f g) → UU (l1 ⊔ l2)
  htpy-is-inverse s t = (pr1 s ~ pr1 t) × (pr2 s ~ pr2 t)

  extensionality-is-inverse :
    {s t : is-inverse f g} → (s ＝ t) ≃ htpy-is-inverse s t
  extensionality-is-inverse {s} {t} =
    equiv-prod equiv-funext equiv-funext ∘e equiv-pair-eq s t

  htpy-eq-is-inverse : {s t : is-inverse f g} → s ＝ t → htpy-is-inverse s t
  htpy-eq-is-inverse = map-equiv extensionality-is-inverse

  eq-htpy-is-inverse : {s t : is-inverse f g} → htpy-is-inverse s t → s ＝ t
  eq-htpy-is-inverse = map-inv-equiv extensionality-is-inverse
```

#### Characterizing equality of `has-inverse`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-has-inverse :
    (s t : has-inverse f) →
    map-inv-has-inverse s ~ map-inv-has-inverse t → UU (l1 ⊔ l2)
  coherence-htpy-has-inverse s t H =
    ( is-retraction-has-inverse s ~ ((f ·l H) ∙h is-retraction-has-inverse t)) ×
    ( is-section-has-inverse s ~ ((H ·r f) ∙h is-section-has-inverse t))

  htpy-has-inverse : (s t : has-inverse f) → UU (l1 ⊔ l2)
  htpy-has-inverse s t =
    Σ ( map-inv-has-inverse s ~ map-inv-has-inverse t)
      ( coherence-htpy-has-inverse s t)

  refl-htpy-has-inverse : (s : has-inverse f) → htpy-has-inverse s s
  pr1 (refl-htpy-has-inverse s) = refl-htpy
  pr1 (pr2 (refl-htpy-has-inverse s)) = refl-htpy
  pr2 (pr2 (refl-htpy-has-inverse s)) = refl-htpy

  htpy-eq-has-inverse : (s t : has-inverse f) → s ＝ t → htpy-has-inverse s t
  htpy-eq-has-inverse s .s refl = refl-htpy-has-inverse s

  is-contr-total-htpy-has-inverse :
    (s : has-inverse f) → is-contr (Σ (has-inverse f) (htpy-has-inverse s))
  is-contr-total-htpy-has-inverse s =
    is-contr-total-Eq-structure
      ( λ x z → coherence-htpy-has-inverse s (x , z))
      ( is-contr-total-htpy (map-inv-has-inverse s))
      ( map-inv-has-inverse s , refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ S R H →
          ( is-section-has-inverse s) ~
          ( is-section-has-inverse (map-inv-has-inverse s , S , R)))
        ( is-contr-total-htpy (is-retraction-has-inverse s))
        ( is-retraction-has-inverse s , refl-htpy)
        ( is-contr-total-htpy (is-section-has-inverse s)))

  is-equiv-htpy-eq-has-inverse :
    (s t : has-inverse f) → is-equiv (htpy-eq-has-inverse s t)
  is-equiv-htpy-eq-has-inverse s =
    fundamental-theorem-id
      ( is-contr-total-htpy-has-inverse s)
      ( htpy-eq-has-inverse s)

  extensionality-has-inverse :
    (s t : has-inverse f) → (s ＝ t) ≃ (htpy-has-inverse s t)
  pr1 (extensionality-has-inverse s t) = htpy-eq-has-inverse s t
  pr2 (extensionality-has-inverse s t) = is-equiv-htpy-eq-has-inverse s t

  eq-htpy-has-inverse : (s t : has-inverse f) → htpy-has-inverse s t → s ＝ t
  eq-htpy-has-inverse s t = map-inv-equiv (extensionality-has-inverse s t)
```

#### Characterizing equality of `invertible-map`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-htpy-invertible-map :
    (s t : invertible-map A B) →
    map-invertible-map s ~ map-invertible-map t →
    map-inv-invertible-map s ~ map-inv-invertible-map t → UU (l1 ⊔ l2)
  coherence-htpy-invertible-map s t H I =
    ( ( is-retraction-map-invertible-map s) ~
      ( htpy-comp-horizontal I H ∙h is-retraction-map-invertible-map t)) ×
    ( ( is-section-map-invertible-map s) ~
      ( htpy-comp-horizontal H I ∙h is-section-map-invertible-map t))

  htpy-invertible-map : (s t : invertible-map A B) → UU (l1 ⊔ l2)
  htpy-invertible-map s t =
    Σ ( map-invertible-map s ~ map-invertible-map t)
      ( λ H →
        Σ ( map-inv-invertible-map s ~ map-inv-invertible-map t)
          ( coherence-htpy-invertible-map s t H))

  refl-htpy-invertible-map : (s : invertible-map A B) → htpy-invertible-map s s
  pr1 (refl-htpy-invertible-map s) = refl-htpy
  pr1 (pr2 (refl-htpy-invertible-map s)) = refl-htpy
  pr1 (pr2 (pr2 (refl-htpy-invertible-map s))) = refl-htpy
  pr2 (pr2 (pr2 (refl-htpy-invertible-map s))) = refl-htpy

  htpy-eq-invertible-map :
    (s t : invertible-map A B) → s ＝ t → htpy-invertible-map s t
  htpy-eq-invertible-map s .s refl = refl-htpy-invertible-map s

  is-contr-total-htpy-invertible-map :
    (s : invertible-map A B) →
    is-contr (Σ (invertible-map A B) (htpy-invertible-map s))
  is-contr-total-htpy-invertible-map s =
    is-contr-total-Eq-structure
      ( λ x z H →
        Σ ( map-inv-invertible-map s ~ map-inv-invertible-map (x , z))
          ( coherence-htpy-invertible-map s (x , z) H))
      ( is-contr-total-htpy (map-invertible-map s))
      ( map-invertible-map s , refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ x z →
          coherence-htpy-invertible-map s
            ( map-invertible-map s , x , z)
            ( refl-htpy))
        ( is-contr-total-htpy (map-inv-invertible-map s))
        ( map-inv-invertible-map s , refl-htpy)
        (is-contr-total-Eq-structure
          ( λ x z a →
            ( is-section-map-invertible-map s) ~
            ( is-section-map-invertible-map
              ( map-invertible-map s , map-inv-invertible-map s , x , z)))
          ( is-contr-total-htpy (is-retraction-map-invertible-map s))
          ( is-retraction-map-invertible-map s , refl-htpy)
          ( is-contr-total-htpy (is-section-map-invertible-map s))))

  is-equiv-htpy-eq-invertible-map :
    (s t : invertible-map A B) → is-equiv (htpy-eq-invertible-map s t)
  is-equiv-htpy-eq-invertible-map s =
    fundamental-theorem-id
      ( is-contr-total-htpy-invertible-map s)
      ( htpy-eq-invertible-map s)

  extensionality-invertible-map :
    (s t : invertible-map A B) → (s ＝ t) ≃ (htpy-invertible-map s t)
  pr1 (extensionality-invertible-map s t) = htpy-eq-invertible-map s t
  pr2 (extensionality-invertible-map s t) = is-equiv-htpy-eq-invertible-map s t

  eq-htpy-invertible-map :
    (s t : invertible-map A B) → htpy-invertible-map s t → s ＝ t
  eq-htpy-invertible-map s t = map-inv-equiv (extensionality-invertible-map s t)
```

### The type `has-inverse id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = id
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = refl-htpy
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = H

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-associative-Σ
        ( A → A)
        ( λ g → (id ∘ g) ~ id)
        ( λ s → (pr1 s ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → (pr1 s ∘ id) ~ id}
        ( is-contr-section-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp-htpy
      ( is-invertible-id-htpy-id-id A)
      ( map-associative-Σ
        ( A → A)
        ( λ g → (id ∘ g) ~ id)
        ( λ s → (pr1 s ∘ id) ~ id))
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-section-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-associative-Σ _ _ _)
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
