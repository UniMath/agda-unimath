# Type arithmetic for cartesian product types

```agda
module foundation-core.type-arithmetic-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels
```

</details>

## Idea

We prove laws for the manipulation of cartesian products with respect to themselves and dependent pair types.

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

  issec-map-inv-commutative-prod :
    (map-commutative-prod ∘ map-inv-commutative-prod) ~ id
  issec-map-inv-commutative-prod (pair b a) = refl

  isretr-map-inv-commutative-prod :
    (map-inv-commutative-prod ∘ map-commutative-prod) ~ id
  isretr-map-inv-commutative-prod (pair a b) = refl

  is-equiv-map-commutative-prod : is-equiv map-commutative-prod
  is-equiv-map-commutative-prod =
    is-equiv-has-inverse
      map-inv-commutative-prod
      issec-map-inv-commutative-prod
      isretr-map-inv-commutative-prod

  commutative-prod : (A × B) ≃ (B × A)
  pr1 commutative-prod = map-commutative-prod
  pr2 commutative-prod = is-equiv-map-commutative-prod
```

### Associativity of cartesian products

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-assoc-prod : (A × B) × C → A × (B × C)
  map-assoc-prod = map-assoc-Σ A (λ x → B) (λ w → C)

  map-inv-assoc-prod : A × (B × C) → (A × B) × C
  map-inv-assoc-prod = map-inv-assoc-Σ A (λ x → B) (λ w → C)

  issec-map-inv-assoc-prod : (map-assoc-prod ∘ map-inv-assoc-prod) ~ id
  issec-map-inv-assoc-prod = issec-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  isretr-map-inv-assoc-prod : (map-inv-assoc-prod ∘ map-assoc-prod) ~ id
  isretr-map-inv-assoc-prod = isretr-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  is-equiv-map-assoc-prod : is-equiv map-assoc-prod
  is-equiv-map-assoc-prod = is-equiv-map-assoc-Σ A (λ x → B) (λ w → C)

  assoc-prod : ((A × B) × C) ≃ (A × (B × C))
  assoc-prod = assoc-Σ A (λ x → B) (λ w → C)
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
