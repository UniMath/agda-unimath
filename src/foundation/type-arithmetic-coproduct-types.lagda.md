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
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-coproduct : A + B → B + A
  map-commutative-coproduct (inl a) = inr a
  map-commutative-coproduct (inr b) = inl b

  map-inv-commutative-coproduct : B + A → A + B
  map-inv-commutative-coproduct (inl b) = inr b
  map-inv-commutative-coproduct (inr a) = inl a

  is-section-map-inv-commutative-coproduct :
    ( map-commutative-coproduct ∘ map-inv-commutative-coproduct) ~ id
  is-section-map-inv-commutative-coproduct (inl b) = refl
  is-section-map-inv-commutative-coproduct (inr a) = refl

  is-retraction-map-inv-commutative-coproduct :
    ( map-inv-commutative-coproduct ∘ map-commutative-coproduct) ~ id
  is-retraction-map-inv-commutative-coproduct (inl a) = refl
  is-retraction-map-inv-commutative-coproduct (inr b) = refl

  is-equiv-map-commutative-coproduct : is-equiv map-commutative-coproduct
  is-equiv-map-commutative-coproduct =
    is-equiv-is-invertible
      map-inv-commutative-coproduct
      is-section-map-inv-commutative-coproduct
      is-retraction-map-inv-commutative-coproduct

  commutative-coproduct : (A + B) ≃ (B + A)
  pr1 commutative-coproduct = map-commutative-coproduct
  pr2 commutative-coproduct = is-equiv-map-commutative-coproduct
```

### Associativity of coproducts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  map-associative-coproduct : (A + B) + C → A + (B + C)
  map-associative-coproduct (inl (inl x)) = inl x
  map-associative-coproduct (inl (inr x)) = inr (inl x)
  map-associative-coproduct (inr x) = inr (inr x)

  map-inv-associative-coproduct : A + (B + C) → (A + B) + C
  map-inv-associative-coproduct (inl x) = inl (inl x)
  map-inv-associative-coproduct (inr (inl x)) = inl (inr x)
  map-inv-associative-coproduct (inr (inr x)) = inr x

  is-section-map-inv-associative-coproduct :
    (map-associative-coproduct ∘ map-inv-associative-coproduct) ~ id
  is-section-map-inv-associative-coproduct (inl x) = refl
  is-section-map-inv-associative-coproduct (inr (inl x)) = refl
  is-section-map-inv-associative-coproduct (inr (inr x)) = refl

  is-retraction-map-inv-associative-coproduct :
    (map-inv-associative-coproduct ∘ map-associative-coproduct) ~ id
  is-retraction-map-inv-associative-coproduct (inl (inl x)) = refl
  is-retraction-map-inv-associative-coproduct (inl (inr x)) = refl
  is-retraction-map-inv-associative-coproduct (inr x) = refl

  is-equiv-map-associative-coproduct : is-equiv map-associative-coproduct
  is-equiv-map-associative-coproduct =
    is-equiv-is-invertible
      map-inv-associative-coproduct
      is-section-map-inv-associative-coproduct
      is-retraction-map-inv-associative-coproduct

  is-equiv-map-inv-associative-coproduct :
    is-equiv map-inv-associative-coproduct
  is-equiv-map-inv-associative-coproduct =
    is-equiv-is-invertible
      map-associative-coproduct
      is-retraction-map-inv-associative-coproduct
      is-section-map-inv-associative-coproduct

  associative-coproduct : ((A + B) + C) ≃ (A + (B + C))
  pr1 associative-coproduct = map-associative-coproduct
  pr2 associative-coproduct = is-equiv-map-associative-coproduct

  inv-associative-coproduct : (A + (B + C)) ≃ ((A + B) + C)
  pr1 inv-associative-coproduct = map-inv-associative-coproduct
  pr2 inv-associative-coproduct = is-equiv-map-inv-associative-coproduct
```

### Right distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : A + B → UU l3)
  where

  map-right-distributive-Σ-coproduct :
    Σ (A + B) C → (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coproduct (inl x , z) = inl (x , z)
  map-right-distributive-Σ-coproduct (inr y , z) = inr (y , z)

  map-inv-right-distributive-Σ-coproduct :
    (Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))) → Σ (A + B) C
  pr1 (map-inv-right-distributive-Σ-coproduct (inl (x , z))) = inl x
  pr2 (map-inv-right-distributive-Σ-coproduct (inl (x , z))) = z
  pr1 (map-inv-right-distributive-Σ-coproduct (inr (y , z))) = inr y
  pr2 (map-inv-right-distributive-Σ-coproduct (inr (y , z))) = z

  is-section-map-inv-right-distributive-Σ-coproduct :
    ( map-right-distributive-Σ-coproduct ∘
      map-inv-right-distributive-Σ-coproduct) ~
    ( id)
  is-section-map-inv-right-distributive-Σ-coproduct (inl (x , z)) = refl
  is-section-map-inv-right-distributive-Σ-coproduct (inr (y , z)) = refl

  is-retraction-map-inv-right-distributive-Σ-coproduct :
    ( map-inv-right-distributive-Σ-coproduct ∘
      map-right-distributive-Σ-coproduct) ~
    ( id)
  is-retraction-map-inv-right-distributive-Σ-coproduct (inl x , z) = refl
  is-retraction-map-inv-right-distributive-Σ-coproduct (inr y , z) = refl

  abstract
    is-equiv-map-right-distributive-Σ-coproduct :
      is-equiv map-right-distributive-Σ-coproduct
    is-equiv-map-right-distributive-Σ-coproduct =
      is-equiv-is-invertible
        map-inv-right-distributive-Σ-coproduct
        is-section-map-inv-right-distributive-Σ-coproduct
        is-retraction-map-inv-right-distributive-Σ-coproduct

  right-distributive-Σ-coproduct :
    Σ (A + B) C ≃ ((Σ A (λ x → C (inl x))) + (Σ B (λ y → C (inr y))))
  pr1 right-distributive-Σ-coproduct = map-right-distributive-Σ-coproduct
  pr2 right-distributive-Σ-coproduct =
    is-equiv-map-right-distributive-Σ-coproduct
```

### Left distributivity of Σ over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3)
  where

  map-left-distributive-Σ-coproduct :
    Σ A (λ x → B x + C x) → (Σ A B) + (Σ A C)
  map-left-distributive-Σ-coproduct (x , inl y) = inl (x , y)
  map-left-distributive-Σ-coproduct (x , inr z) = inr (x , z)

  map-inv-left-distributive-Σ-coproduct :
    (Σ A B) + (Σ A C) → Σ A (λ x → B x + C x)
  pr1 (map-inv-left-distributive-Σ-coproduct (inl (x , y))) = x
  pr2 (map-inv-left-distributive-Σ-coproduct (inl (x , y))) = inl y
  pr1 (map-inv-left-distributive-Σ-coproduct (inr (x , z))) = x
  pr2 (map-inv-left-distributive-Σ-coproduct (inr (x , z))) = inr z

  is-section-map-inv-left-distributive-Σ-coproduct :
    ( map-left-distributive-Σ-coproduct ∘
      map-inv-left-distributive-Σ-coproduct) ~
    ( id)
  is-section-map-inv-left-distributive-Σ-coproduct (inl (x , y)) = refl
  is-section-map-inv-left-distributive-Σ-coproduct (inr (x , z)) = refl

  is-retraction-map-inv-left-distributive-Σ-coproduct :
    ( map-inv-left-distributive-Σ-coproduct ∘
      map-left-distributive-Σ-coproduct) ~
    ( id)
  is-retraction-map-inv-left-distributive-Σ-coproduct (x , inl y) = refl
  is-retraction-map-inv-left-distributive-Σ-coproduct (x , inr z) = refl

  is-equiv-map-left-distributive-Σ-coproduct :
    is-equiv map-left-distributive-Σ-coproduct
  is-equiv-map-left-distributive-Σ-coproduct =
    is-equiv-is-invertible
      map-inv-left-distributive-Σ-coproduct
      is-section-map-inv-left-distributive-Σ-coproduct
      is-retraction-map-inv-left-distributive-Σ-coproduct

  left-distributive-Σ-coproduct :
    Σ A (λ x → B x + C x) ≃ ((Σ A B) + (Σ A C))
  pr1 left-distributive-Σ-coproduct = map-left-distributive-Σ-coproduct
  pr2 left-distributive-Σ-coproduct = is-equiv-map-left-distributive-Σ-coproduct
```

### Right distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-right-distributive-product-coproduct : (A + B) × C → (A × C) + (B × C)
  map-right-distributive-product-coproduct =
    map-right-distributive-Σ-coproduct (λ _ → C)

  map-inv-right-distributive-product-coproduct :
    (A × C) + (B × C) → (A + B) × C
  map-inv-right-distributive-product-coproduct =
    map-inv-right-distributive-Σ-coproduct (λ _ → C)

  is-section-map-inv-right-distributive-product-coproduct :
    map-right-distributive-product-coproduct ∘
    map-inv-right-distributive-product-coproduct ~ id
  is-section-map-inv-right-distributive-product-coproduct =
    is-section-map-inv-right-distributive-Σ-coproduct (λ _ → C)

  is-retraction-map-inv-right-distributive-product-coproduct :
    map-inv-right-distributive-product-coproduct ∘
    map-right-distributive-product-coproduct ~ id
  is-retraction-map-inv-right-distributive-product-coproduct =
    is-retraction-map-inv-right-distributive-Σ-coproduct (λ _ → C)

  abstract
    is-equiv-map-right-distributive-product-coproduct :
      is-equiv map-right-distributive-product-coproduct
    is-equiv-map-right-distributive-product-coproduct =
      is-equiv-map-right-distributive-Σ-coproduct (λ _ → C)

  right-distributive-product-coproduct : ((A + B) × C) ≃ ((A × C) + (B × C))
  right-distributive-product-coproduct =
    right-distributive-Σ-coproduct (λ _ → C)
```

### Left distributivity of products over coproducts

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-left-distributive-product-coproduct : A × (B + C) → (A × B) + (A × C)
  map-left-distributive-product-coproduct =
    map-left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)

  map-inv-left-distributive-product-coproduct :
    (A × B) + (A × C) → A × (B + C)
  map-inv-left-distributive-product-coproduct =
    map-inv-left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)

  is-section-map-inv-left-distributive-product-coproduct :
    map-left-distributive-product-coproduct ∘
    map-inv-left-distributive-product-coproduct ~ id
  is-section-map-inv-left-distributive-product-coproduct =
    is-section-map-inv-left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)

  is-retraction-map-inv-left-distributive-product-coproduct :
    map-inv-left-distributive-product-coproduct ∘
    map-left-distributive-product-coproduct ~ id
  is-retraction-map-inv-left-distributive-product-coproduct =
    is-retraction-map-inv-left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)

  is-equiv-map-left-distributive-product-coproduct :
    is-equiv map-left-distributive-product-coproduct
  is-equiv-map-left-distributive-product-coproduct =
    is-equiv-map-left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)

  left-distributive-product-coproduct : (A × (B + C)) ≃ ((A × B) + (A × C))
  left-distributive-product-coproduct =
    left-distributive-Σ-coproduct A (λ _ → B) (λ _ → C)
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

  is-empty-left-summand-is-contr-coproduct :
    is-contr (A + B) → B → is-empty A
  is-empty-left-summand-is-contr-coproduct H b a =
    ex-falso (is-empty-eq-coproduct-inl-inr a b (eq-is-contr H))

  is-empty-right-summand-is-contr-coproduct :
    is-contr (A + B) → A → is-empty B
  is-empty-right-summand-is-contr-coproduct H a b =
    ex-falso (is-empty-eq-coproduct-inl-inr a b (eq-is-contr H))
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
