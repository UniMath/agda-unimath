# Type arithmetic for coproduct types

```agda
module foundation.type-arithmetic-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-coproduct-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove laws for the manipulation of coproduct types with respect to
themselves, cartesian products, and dependent pair types.

## Laws

### Commutativity of coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  map-commutative-coprod : A + B → B + A
  map-commutative-coprod (inl a) = inr a
  map-commutative-coprod (inr b) = inl b

  map-inv-commutative-coprod : B + A → A + B
  map-inv-commutative-coprod (inl b) = inr b
  map-inv-commutative-coprod (inr a) = inl a

  is-section-map-inv-commutative-coprod :
    ( map-commutative-coprod ∘ map-inv-commutative-coprod) ~ id
  is-section-map-inv-commutative-coprod (inl b) = refl
  is-section-map-inv-commutative-coprod (inr a) = refl

  is-retraction-map-inv-commutative-coprod :
    ( map-inv-commutative-coprod ∘ map-commutative-coprod) ~ id
  is-retraction-map-inv-commutative-coprod (inl a) = refl
  is-retraction-map-inv-commutative-coprod (inr b) = refl

  is-equiv-map-commutative-coprod : is-equiv map-commutative-coprod
  is-equiv-map-commutative-coprod =
    is-equiv-has-inverse
      map-inv-commutative-coprod
      is-section-map-inv-commutative-coprod
      is-retraction-map-inv-commutative-coprod

  commutative-coprod : (A + B) ≃ (B + A)
  pr1 commutative-coprod = map-commutative-coprod
  pr2 commutative-coprod = is-equiv-map-commutative-coprod
```

### Associativity of coproducts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  map-associative-coprod : (A + B) + C → A + (B + C)
  map-associative-coprod (inl (inl x)) = inl x
  map-associative-coprod (inl (inr x)) = inr (inl x)
  map-associative-coprod (inr x) = inr (inr x)

  map-inv-associative-coprod : A + (B + C) → (A + B) + C
  map-inv-associative-coprod (inl x) = inl (inl x)
  map-inv-associative-coprod (inr (inl x)) = inl (inr x)
  map-inv-associative-coprod (inr (inr x)) = inr x

  is-section-map-inv-associative-coprod :
    (map-associative-coprod ∘ map-inv-associative-coprod) ~ id
  is-section-map-inv-associative-coprod (inl x) = refl
  is-section-map-inv-associative-coprod (inr (inl x)) = refl
  is-section-map-inv-associative-coprod (inr (inr x)) = refl

  is-retraction-map-inv-associative-coprod :
    (map-inv-associative-coprod ∘ map-associative-coprod) ~ id
  is-retraction-map-inv-associative-coprod (inl (inl x)) = refl
  is-retraction-map-inv-associative-coprod (inl (inr x)) = refl
  is-retraction-map-inv-associative-coprod (inr x) = refl

  is-equiv-map-associative-coprod : is-equiv map-associative-coprod
  is-equiv-map-associative-coprod =
    is-equiv-has-inverse
      map-inv-associative-coprod
      is-section-map-inv-associative-coprod
      is-retraction-map-inv-associative-coprod

  is-equiv-map-inv-associative-coprod : is-equiv map-inv-associative-coprod
  is-equiv-map-inv-associative-coprod =
    is-equiv-has-inverse
      map-associative-coprod
      is-retraction-map-inv-associative-coprod
      is-section-map-inv-associative-coprod

  associative-coprod : ((A + B) + C) ≃ (A + (B + C))
  pr1 associative-coprod = map-associative-coprod
  pr2 associative-coprod = is-equiv-map-associative-coprod

  inv-associative-coprod : (A + (B + C)) ≃ ((A + B) + C)
  pr1 inv-associative-coprod = map-inv-associative-coprod
  pr2 inv-associative-coprod = is-equiv-map-inv-associative-coprod
```

### Right distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : A + B → UU l3)
  where

  map-right-distributive-Σ-coprod :
    Σ (A + B) C → (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coprod (pair (inl x) z) = inl (pair x z)
  map-right-distributive-Σ-coprod (pair (inr y) z) = inr (pair y z)

  map-inv-right-distributive-Σ-coprod :
    (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))) → Σ (A + B) C
  pr1 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = inl x
  pr2 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = z
  pr1 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = inr y
  pr2 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = z

  is-section-map-inv-right-distributive-Σ-coprod :
    ( map-right-distributive-Σ-coprod ∘ map-inv-right-distributive-Σ-coprod) ~
    ( id)
  is-section-map-inv-right-distributive-Σ-coprod (inl (pair x z)) = refl
  is-section-map-inv-right-distributive-Σ-coprod (inr (pair y z)) = refl

  is-retraction-map-inv-right-distributive-Σ-coprod :
    ( map-inv-right-distributive-Σ-coprod ∘ map-right-distributive-Σ-coprod) ~
    ( id)
  is-retraction-map-inv-right-distributive-Σ-coprod (pair (inl x) z) = refl
  is-retraction-map-inv-right-distributive-Σ-coprod (pair (inr y) z) = refl

  abstract
    is-equiv-map-right-distributive-Σ-coprod :
      is-equiv map-right-distributive-Σ-coprod
    is-equiv-map-right-distributive-Σ-coprod =
      is-equiv-has-inverse
        map-inv-right-distributive-Σ-coprod
        is-section-map-inv-right-distributive-Σ-coprod
        is-retraction-map-inv-right-distributive-Σ-coprod

  right-distributive-Σ-coprod :
    Σ (A + B) C ≃ ((Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))))
  pr1 right-distributive-Σ-coprod = map-right-distributive-Σ-coprod
  pr2 right-distributive-Σ-coprod = is-equiv-map-right-distributive-Σ-coprod
```

### Left distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3)
  where

  map-left-distributive-Σ-coprod :
    Σ A (λ x → B x + C x) → (Σ A B) + (Σ A C)
  map-left-distributive-Σ-coprod (pair x (inl y)) = inl (pair x y)
  map-left-distributive-Σ-coprod (pair x (inr z)) = inr (pair x z)

  map-inv-left-distributive-Σ-coprod :
    (Σ A B) + (Σ A C) → Σ A (λ x → B x + C x)
  pr1 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = inl y
  pr1 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = inr z

  is-section-map-inv-left-distributive-Σ-coprod :
    ( map-left-distributive-Σ-coprod ∘ map-inv-left-distributive-Σ-coprod) ~ id
  is-section-map-inv-left-distributive-Σ-coprod (inl (pair x y)) = refl
  is-section-map-inv-left-distributive-Σ-coprod (inr (pair x z)) = refl

  is-retraction-map-inv-left-distributive-Σ-coprod :
    ( map-inv-left-distributive-Σ-coprod ∘ map-left-distributive-Σ-coprod) ~ id
  is-retraction-map-inv-left-distributive-Σ-coprod (pair x (inl y)) = refl
  is-retraction-map-inv-left-distributive-Σ-coprod (pair x (inr z)) = refl

  is-equiv-map-left-distributive-Σ-coprod :
    is-equiv map-left-distributive-Σ-coprod
  is-equiv-map-left-distributive-Σ-coprod =
    is-equiv-has-inverse
      map-inv-left-distributive-Σ-coprod
      is-section-map-inv-left-distributive-Σ-coprod
      is-retraction-map-inv-left-distributive-Σ-coprod

  left-distributive-Σ-coprod :
    Σ A (λ x → B x + C x) ≃ ((Σ A B) + (Σ A C))
  pr1 left-distributive-Σ-coprod = map-left-distributive-Σ-coprod
  pr2 left-distributive-Σ-coprod = is-equiv-map-left-distributive-Σ-coprod
```

### Right distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-right-distributive-prod-coprod : (A + B) × C → (A × C) + (B × C)
  map-right-distributive-prod-coprod =
    map-right-distributive-Σ-coprod A B (λ x → C)

  map-inv-right-distributive-prod-coprod :
    (A × C) + (B × C) → (A + B) × C
  map-inv-right-distributive-prod-coprod =
    map-inv-right-distributive-Σ-coprod A B (λ x → C)

  is-section-map-inv-right-distributive-prod-coprod :
    ( map-right-distributive-prod-coprod ∘
      map-inv-right-distributive-prod-coprod) ~ id
  is-section-map-inv-right-distributive-prod-coprod =
    is-section-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  is-retraction-map-inv-right-distributive-prod-coprod :
    ( map-inv-right-distributive-prod-coprod ∘
      map-right-distributive-prod-coprod) ~ id
  is-retraction-map-inv-right-distributive-prod-coprod =
    is-retraction-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  abstract
    is-equiv-map-right-distributive-prod-coprod :
      is-equiv map-right-distributive-prod-coprod
    is-equiv-map-right-distributive-prod-coprod =
      is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)

  right-distributive-prod-coprod : ((A + B) × C) ≃ ((A × C) + (B × C))
  right-distributive-prod-coprod = right-distributive-Σ-coprod A B (λ x → C)
```

### Left distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-left-distributive-prod-coprod : A × (B + C) → (A × B) + (A × C)
  map-left-distributive-prod-coprod =
    map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  map-inv-left-distributive-prod-coprod :
    (A × B) + (A × C) → A × (B + C)
  map-inv-left-distributive-prod-coprod =
    map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-section-map-inv-left-distributive-prod-coprod :
    ( map-left-distributive-prod-coprod ∘
      map-inv-left-distributive-prod-coprod) ~ id
  is-section-map-inv-left-distributive-prod-coprod =
    is-section-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-retraction-map-inv-left-distributive-prod-coprod :
    ( map-inv-left-distributive-prod-coprod ∘
      map-left-distributive-prod-coprod) ~ id
  is-retraction-map-inv-left-distributive-prod-coprod =
    is-retraction-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-equiv-map-left-distributive-prod-coprod :
    is-equiv map-left-distributive-prod-coprod
  is-equiv-map-left-distributive-prod-coprod =
    is-equiv-map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  left-distributive-prod-coprod : (A × (B + C)) ≃ ((A × B) + (A × C))
  left-distributive-prod-coprod =
    left-distributive-Σ-coprod A (λ x → B) (λ x → C)
```

### If a coproduct is contractible then one summand is contractible and the other is empty

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-left-summand :
    is-contr (A + B) → A → is-contr A
  pr1 (is-contr-left-summand H a) = a
  pr2 (is-contr-left-summand H a) x =
    is-injective-inl (eq-is-contr H {inl a} {inl x})

  is-contr-left-summand-is-empty :
    is-contr (A + B) → is-empty B → is-contr A
  pr1 (is-contr-left-summand-is-empty (inl a , H) K) = a
  pr2 (is-contr-left-summand-is-empty (inl a , H) K) x =
    is-injective-inl (H (inl x))
  is-contr-left-summand-is-empty (inr b , H) K = ex-falso (K b)

  is-contr-right-summand :
    is-contr (A + B) → B → is-contr B
  pr1 (is-contr-right-summand H b) = b
  pr2 (is-contr-right-summand H b) x =
    is-injective-inr (eq-is-contr H {inr b} {inr x})

  is-contr-right-summand-is-empty :
    is-contr (A + B) → is-empty A → is-contr B
  is-contr-right-summand-is-empty (inl a , H) K = ex-falso (K a)
  pr1 (is-contr-right-summand-is-empty (inr b , H) K) = b
  pr2 (is-contr-right-summand-is-empty (inr b , H) K) x =
    is-injective-inr (H (inr x))

  is-empty-left-summand-is-contr-coprod :
    is-contr (A + B) → B → is-empty A
  is-empty-left-summand-is-contr-coprod H b a =
    ex-falso (is-empty-eq-coprod-inl-inr a b (eq-is-contr H))

  is-empty-right-summand-is-contr-coprod :
    is-contr (A + B) → A → is-empty B
  is-empty-right-summand-is-contr-coprod H a b =
    ex-falso (is-empty-eq-coprod-inl-inr a b (eq-is-contr H))
```

## See also

- Functorial properties of coproducts are recorded in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).
- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- The universal property of coproducts is treated in
  [`foundation.universal-property-coproduct-types`](foundation.universal-property-coproduct-types.md).

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Arithmetical laws involving cartesian-product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
