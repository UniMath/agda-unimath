# Type arithmetic for cartesian product types

```agda
module foundation.type-arithmetic-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

We prove laws for the manipulation of cartesian products with respect to
themselves and dependent pair types.

## Laws

### Commutativity of cartesian products

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-prod : A × B → B × A
  pr1 (map-commutative-prod (pair a b)) = b
  pr2 (map-commutative-prod (pair a b)) = a

  map-inv-commutative-prod : B × A → A × B
  pr1 (map-inv-commutative-prod (pair b a)) = a
  pr2 (map-inv-commutative-prod (pair b a)) = b

  is-section-map-inv-commutative-prod :
    (map-commutative-prod ∘ map-inv-commutative-prod) ~ id
  is-section-map-inv-commutative-prod (pair b a) = refl

  is-retraction-map-inv-commutative-prod :
    (map-inv-commutative-prod ∘ map-commutative-prod) ~ id
  is-retraction-map-inv-commutative-prod (pair a b) = refl

  is-equiv-map-commutative-prod : is-equiv map-commutative-prod
  is-equiv-map-commutative-prod =
    is-equiv-is-invertible
      map-inv-commutative-prod
      is-section-map-inv-commutative-prod
      is-retraction-map-inv-commutative-prod

  commutative-prod : (A × B) ≃ (B × A)
  pr1 commutative-prod = map-commutative-prod
  pr2 commutative-prod = is-equiv-map-commutative-prod
```

### Associativity of cartesian products

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-associative-prod : (A × B) × C → A × (B × C)
  map-associative-prod = map-associative-Σ A (λ x → B) (λ w → C)

  map-inv-associative-prod : A × (B × C) → (A × B) × C
  map-inv-associative-prod = map-inv-associative-Σ A (λ x → B) (λ w → C)

  is-section-map-inv-associative-prod :
    (map-associative-prod ∘ map-inv-associative-prod) ~ id
  is-section-map-inv-associative-prod =
    is-section-map-inv-associative-Σ A (λ x → B) (λ w → C)

  is-retraction-map-inv-associative-prod :
    (map-inv-associative-prod ∘ map-associative-prod) ~ id
  is-retraction-map-inv-associative-prod =
    is-retraction-map-inv-associative-Σ A (λ x → B) (λ w → C)

  is-equiv-map-associative-prod : is-equiv map-associative-prod
  is-equiv-map-associative-prod =
    is-equiv-map-associative-Σ A (λ x → B) (λ w → C)

  associative-prod : ((A × B) × C) ≃ (A × (B × C))
  associative-prod = associative-Σ A (λ x → B) (λ w → C)
```

### The unit laws of cartesian product types with respect to contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-B : is-contr B)
  where

  right-unit-law-prod-is-contr : (A × B) ≃ A
  right-unit-law-prod-is-contr = right-unit-law-Σ-is-contr (λ a → is-contr-B)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-A : is-contr A)
  where

  left-unit-law-prod-is-contr : (A × B) ≃ B
  left-unit-law-prod-is-contr =
    left-unit-law-Σ-is-contr is-contr-A (center is-contr-A)

  is-equiv-pr2-prod-is-contr : is-equiv (pr2 {B = λ a → B})
  is-equiv-pr2-prod-is-contr =
    is-equiv-comp
      ( pr1)
      ( map-commutative-prod)
      ( is-equiv-map-commutative-prod)
      ( is-equiv-pr1-is-contr λ b → is-contr-A)

  equiv-pr2-prod-is-contr : (A × B) ≃ B
  pr1 equiv-pr2-prod-is-contr = pr2
  pr2 equiv-pr2-prod-is-contr = is-equiv-pr2-prod-is-contr
```

### Adding redundant property

```agda
equiv-add-redundant-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (is-prop B) → (f : A → B) → (A ≃ (A × B))
pr1 (equiv-add-redundant-prop is-prop-B f) a = a , f a
pr2 (equiv-add-redundant-prop is-prop-B f) =
  is-equiv-is-invertible
    ( pr1)
    ( λ p → eq-pair refl (eq-is-prop is-prop-B))
    ( λ a → refl)
```

## See also

- Functorial properties of cartesian products are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- The universal property of cartesian product types is treated in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
  - Arithmetical laws involving dependent product types are recorded in
    [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
