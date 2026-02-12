# Type arithmetic for dependent pair types

```agda
module foundation.type-arithmetic-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.singleton-induction
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

We prove laws for the manipulation of dependent pair types with respect to
themselves and arithmetical laws with respect to contractible types.

## Properties

### The left unit law for Σ using a contractible base type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = a
  pr2 (map-inv-left-unit-law-Σ-is-contr b) = b

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr =
    ind-Σ (ind-singleton a C (λ x → B x → B a) (id))

  is-section-map-inv-left-unit-law-Σ-is-contr :
    map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr ~ id
  is-section-map-inv-left-unit-law-Σ-is-contr b =
    ap
      ( λ (f : B a → B a) → f b)
      ( compute-ind-singleton a C (λ x → B x → B a) id)

  is-retraction-map-inv-left-unit-law-Σ-is-contr :
    map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr ~ id
  is-retraction-map-inv-left-unit-law-Σ-is-contr =
    ind-Σ
      ( ind-singleton a C
        ( λ x →
          ( y : B x) →
          map-inv-left-unit-law-Σ-is-contr
            ( map-left-unit-law-Σ-is-contr (x , y)) ＝
          ( x , y))
        ( λ y → ap
          ( map-inv-left-unit-law-Σ-is-contr)
          ( ap (λ f → f y) ( compute-ind-singleton a C (λ x → B x → B a) id))))

  is-equiv-map-left-unit-law-Σ-is-contr :
    is-equiv map-left-unit-law-Σ-is-contr
  is-equiv-map-left-unit-law-Σ-is-contr =
    is-equiv-is-invertible
      map-inv-left-unit-law-Σ-is-contr
      is-section-map-inv-left-unit-law-Σ-is-contr
      is-retraction-map-inv-left-unit-law-Σ-is-contr

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = map-left-unit-law-Σ-is-contr
  pr2 left-unit-law-Σ-is-contr = is-equiv-map-left-unit-law-Σ-is-contr

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr =
      is-equiv-is-invertible
        map-left-unit-law-Σ-is-contr
        is-retraction-map-inv-left-unit-law-Σ-is-contr
        is-section-map-inv-left-unit-law-Σ-is-contr

  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = map-inv-left-unit-law-Σ-is-contr
  pr2 inv-left-unit-law-Σ-is-contr = is-equiv-map-inv-left-unit-law-Σ-is-contr
```

### Right unit law for dependent pair types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-equiv-pr1-is-contr : ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
    is-equiv-pr1-is-contr is-contr-B =
      is-equiv-is-contr-map
        ( λ x → is-contr-equiv
          ( B x)
          ( equiv-fiber-pr1 B x)
          ( is-contr-B x))

  equiv-pr1 : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  pr1 (equiv-pr1 is-contr-B) = pr1
  pr2 (equiv-pr1 is-contr-B) = is-equiv-pr1-is-contr is-contr-B

  right-unit-law-Σ-is-contr : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  right-unit-law-Σ-is-contr = equiv-pr1

  abstract
    is-contr-is-equiv-pr1 : is-equiv (pr1 {B = B}) → ((a : A) → is-contr (B a))
    is-contr-is-equiv-pr1 is-equiv-pr1-B a =
      is-contr-equiv'
        ( fiber pr1 a)
        ( equiv-fiber-pr1 B a)
        ( is-contr-map-is-equiv is-equiv-pr1-B a)

  map-inv-right-unit-law-Σ-is-contr :
    ((a : A) → is-contr (B a)) → A → Σ A B
  map-inv-right-unit-law-Σ-is-contr H a = (a , center (H a))

  is-section-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    pr1 ∘ map-inv-right-unit-law-Σ-is-contr H ~ id
  is-section-map-inv-right-unit-law-Σ-is-contr H = refl-htpy

  is-retraction-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    map-inv-right-unit-law-Σ-is-contr H ∘ pr1 ~ id
  is-retraction-map-inv-right-unit-law-Σ-is-contr H (a , b) =
    eq-pair-eq-fiber (eq-is-contr (H a))

  is-equiv-map-inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) →
    is-equiv (map-inv-right-unit-law-Σ-is-contr H)
  is-equiv-map-inv-right-unit-law-Σ-is-contr H =
    is-equiv-is-invertible
      ( pr1)
      ( is-retraction-map-inv-right-unit-law-Σ-is-contr H)
      ( is-section-map-inv-right-unit-law-Σ-is-contr H)

  inv-right-unit-law-Σ-is-contr :
    (H : (a : A) → is-contr (B a)) → A ≃ Σ A B
  pr1 (inv-right-unit-law-Σ-is-contr H) = map-inv-right-unit-law-Σ-is-contr H
  pr2 (inv-right-unit-law-Σ-is-contr H) =
    is-equiv-map-inv-right-unit-law-Σ-is-contr H
```

### Associativity of dependent pair types

There are two ways to express associativity for dependent pair types. We
formalize both ways.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3}
  where

  map-associative-Σ : Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (x , y)))
  pr1 (map-associative-Σ ((x , y) , z)) = x
  pr1 (pr2 (map-associative-Σ ((x , y) , z))) = y
  pr2 (pr2 (map-associative-Σ ((x , y) , z))) = z

  map-inv-associative-Σ : Σ A (λ x → Σ (B x) (λ y → C (x , y))) → Σ (Σ A B) C
  pr1 (pr1 (map-inv-associative-Σ (x , y , z))) = x
  pr2 (pr1 (map-inv-associative-Σ (x , y , z))) = y
  pr2 (map-inv-associative-Σ (x , y , z)) = z

  is-retraction-map-inv-associative-Σ :
    map-inv-associative-Σ ∘ map-associative-Σ ~ id
  is-retraction-map-inv-associative-Σ ((x , y) , z) = refl

  is-section-map-inv-associative-Σ :
    map-associative-Σ ∘ map-inv-associative-Σ ~ id
  is-section-map-inv-associative-Σ (x , (y , z)) = refl

  is-equiv-map-associative-Σ : is-equiv map-associative-Σ
  is-equiv-map-associative-Σ =
    is-equiv-is-invertible
      map-inv-associative-Σ
      is-section-map-inv-associative-Σ
      is-retraction-map-inv-associative-Σ

  associative-Σ : Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (x , y)))
  pr1 associative-Σ = map-associative-Σ
  pr2 associative-Σ = is-equiv-map-associative-Σ

  is-equiv-map-inv-associative-Σ : is-equiv map-inv-associative-Σ
  is-equiv-map-inv-associative-Σ =
    is-equiv-is-invertible
      map-associative-Σ
      is-retraction-map-inv-associative-Σ
      is-section-map-inv-associative-Σ

  inv-associative-Σ : Σ A (λ x → Σ (B x) (λ y → C (x , y))) ≃ Σ (Σ A B) C
  pr1 inv-associative-Σ = map-inv-associative-Σ
  pr2 inv-associative-Σ = is-equiv-map-inv-associative-Σ
```

### Associativity, second formulation

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3)
  where

  map-associative-Σ' :
    Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) → Σ A (λ x → Σ (B x) (C x))
  pr1 (map-associative-Σ' ((x , y) , z)) = x
  pr1 (pr2 (map-associative-Σ' ((x , y) , z))) = y
  pr2 (pr2 (map-associative-Σ' ((x , y) , z))) = z

  map-inv-associative-Σ' :
    Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  pr1 (pr1 (map-inv-associative-Σ' (x , y , z))) = x
  pr2 (pr1 (map-inv-associative-Σ' (x , y , z))) = y
  pr2 (map-inv-associative-Σ' (x , y , z)) = z

  is-section-map-inv-associative-Σ' :
    map-associative-Σ' ∘ map-inv-associative-Σ' ~ id
  is-section-map-inv-associative-Σ' (x , (y , z)) = refl

  is-retraction-map-inv-associative-Σ' :
    map-inv-associative-Σ' ∘ map-associative-Σ' ~ id
  is-retraction-map-inv-associative-Σ' ((x , y) , z) = refl

  is-equiv-map-associative-Σ' : is-equiv map-associative-Σ'
  is-equiv-map-associative-Σ' =
    is-equiv-is-invertible
      map-inv-associative-Σ'
      is-section-map-inv-associative-Σ'
      is-retraction-map-inv-associative-Σ'

  associative-Σ' :
    Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) ≃ Σ A (λ x → Σ (B x) (C x))
  pr1 associative-Σ' = map-associative-Σ'
  pr2 associative-Σ' = is-equiv-map-associative-Σ'

  inv-associative-Σ' :
    Σ A (λ x → Σ (B x) (C x)) ≃ Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  pr1 inv-associative-Σ' = map-inv-associative-Σ'
  pr2 inv-associative-Σ' =
    is-equiv-is-invertible
      map-associative-Σ'
      is-retraction-map-inv-associative-Σ'
      is-section-map-inv-associative-Σ'
```

### The interchange law

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where

  map-interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 (pr1 (map-interchange-Σ-Σ t)) = pr1 (pr1 t)
  pr2 (pr1 (map-interchange-Σ-Σ t)) = pr1 (pr2 t)
  pr1 (pr2 (map-interchange-Σ-Σ t)) = pr2 (pr1 t)
  pr2 (pr2 (map-interchange-Σ-Σ t)) = pr2 (pr2 t)

  map-inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 (pr1 (map-inv-interchange-Σ-Σ t)) = pr1 (pr1 t)
  pr2 (pr1 (map-inv-interchange-Σ-Σ t)) = pr1 (pr2 t)
  pr1 (pr2 (map-inv-interchange-Σ-Σ t)) = pr2 (pr1 t)
  pr2 (pr2 (map-inv-interchange-Σ-Σ t)) = pr2 (pr2 t)

  is-section-map-inv-interchange-Σ-Σ :
    map-interchange-Σ-Σ ∘ map-inv-interchange-Σ-Σ ~ id
  is-section-map-inv-interchange-Σ-Σ ((a , c) , (b , d)) = refl

  is-retraction-map-inv-interchange-Σ-Σ :
    map-inv-interchange-Σ-Σ ∘ map-interchange-Σ-Σ ~ id
  is-retraction-map-inv-interchange-Σ-Σ ((a , b) , (c , d)) = refl

  is-equiv-map-interchange-Σ-Σ : is-equiv map-interchange-Σ-Σ
  is-equiv-map-interchange-Σ-Σ =
    is-equiv-is-invertible
      map-inv-interchange-Σ-Σ
      is-section-map-inv-interchange-Σ-Σ
      is-retraction-map-inv-interchange-Σ-Σ

  is-equiv-map-inv-interchange-Σ-Σ : is-equiv map-inv-interchange-Σ-Σ
  is-equiv-map-inv-interchange-Σ-Σ =
    is-equiv-is-invertible
      map-interchange-Σ-Σ
      is-retraction-map-inv-interchange-Σ-Σ
      is-section-map-inv-interchange-Σ-Σ

  interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) ≃
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 interchange-Σ-Σ = map-interchange-Σ-Σ
  pr2 interchange-Σ-Σ = is-equiv-map-interchange-Σ-Σ

  inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) ≃
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 inv-interchange-Σ-Σ = map-inv-interchange-Σ-Σ
  pr2 inv-interchange-Σ-Σ = is-equiv-map-inv-interchange-Σ-Σ

  interchange-Σ-Σ-Σ :
    Σ A (λ x → Σ (B x) (λ y → Σ (C x) (D x y))) ≃
    Σ A (λ x → Σ (C x) (λ z → Σ (B x) (λ y → D x y z)))
  interchange-Σ-Σ-Σ =
    associative-Σ' A C (λ x z → Σ (B x) λ y → D x y z) ∘e
    interchange-Σ-Σ ∘e
    inv-associative-Σ' A B (λ x y → Σ (C x) (D x y))

  eq-interchange-Σ-Σ-is-contr :
    {a : A} {b : B a} → is-torsorial (D a b) →
    {x y : Σ (C a) (D a b)} →
    map-equiv interchange-Σ-Σ ((a , b) , x) ＝
    map-equiv interchange-Σ-Σ ((a , b) , y)
  eq-interchange-Σ-Σ-is-contr H =
    ap (map-equiv interchange-Σ-Σ) (eq-pair-eq-fiber (eq-is-contr H))
```

### Swapping the order of quantification in a Σ-type, on the left

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (a , b , c)) = b
  pr1 (pr2 (map-left-swap-Σ (a , b , c))) = a
  pr2 (pr2 (map-left-swap-Σ (a , b , c))) = c

  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (b , a , c)) = a
  pr1 (pr2 (map-inv-left-swap-Σ (b , a , c))) = b
  pr2 (pr2 (map-inv-left-swap-Σ (b , a , c))) = c

  is-retraction-map-inv-left-swap-Σ :
    map-inv-left-swap-Σ ∘ map-left-swap-Σ ~ id
  is-retraction-map-inv-left-swap-Σ (a , (b , c)) = refl

  is-section-map-inv-left-swap-Σ : map-left-swap-Σ ∘ map-inv-left-swap-Σ ~ id
  is-section-map-inv-left-swap-Σ (b , (a , c)) = refl

  is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
  is-equiv-map-left-swap-Σ =
    is-equiv-is-invertible
      map-inv-left-swap-Σ
      is-section-map-inv-left-swap-Σ
      is-retraction-map-inv-left-swap-Σ

  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = map-left-swap-Σ
  pr2 equiv-left-swap-Σ = is-equiv-map-left-swap-Σ
```

### Swapping the order of quantification in a Σ-type, on the right

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  pr1 (pr1 (map-right-swap-Σ ((a , b) , c))) = a
  pr2 (pr1 (map-right-swap-Σ ((a , b) , c))) = c
  pr2 (map-right-swap-Σ ((a , b) , c)) = b

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  pr1 (pr1 (map-inv-right-swap-Σ ((a , c) , b))) = a
  pr2 (pr1 (map-inv-right-swap-Σ ((a , c) , b))) = b
  pr2 (map-inv-right-swap-Σ ((a , c) , b)) = c

  is-section-map-inv-right-swap-Σ :
    map-right-swap-Σ ∘ map-inv-right-swap-Σ ~ id
  is-section-map-inv-right-swap-Σ ((x , y) , z) = refl

  is-retraction-map-inv-right-swap-Σ :
    map-inv-right-swap-Σ ∘ map-right-swap-Σ ~ id
  is-retraction-map-inv-right-swap-Σ ((x , z) , y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-is-invertible
      map-inv-right-swap-Σ
      is-section-map-inv-right-swap-Σ
      is-retraction-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  pr1 equiv-right-swap-Σ = map-right-swap-Σ
  pr2 equiv-right-swap-Σ = is-equiv-map-right-swap-Σ
```

### Distributive laws of cartesian products over Σ

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  where

  left-distributive-product-Σ : A × (Σ B C) ≃ Σ B (λ b → A × (C b))
  left-distributive-product-Σ = equiv-left-swap-Σ

  inv-left-distributive-product-Σ : Σ B (λ b → A × (C b)) ≃ A × (Σ B C)
  inv-left-distributive-product-Σ = equiv-left-swap-Σ

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
  where

  right-distributive-product-Σ : (Σ A B) × C ≃ Σ A (λ a → B a × C)
  right-distributive-product-Σ = associative-Σ

  inv-right-distributive-product-Σ : Σ A (λ a → B a × C) ≃ (Σ A B) × C
  inv-right-distributive-product-Σ = inv-associative-Σ

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  where

  distributive-product-Σ :
    (Σ A B) × (Σ C D) ≃ Σ (A × C) (λ (a , c) → B a × D c)
  distributive-product-Σ = interchange-Σ-Σ (λ _ _ → D)

  inv-distributive-product-Σ :
    Σ (A × C) (λ (a , c) → B a × D c) ≃ (Σ A B) × (Σ C D)
  inv-distributive-product-Σ = inv-interchange-Σ-Σ (λ _ _ → D)
```

## See also

- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).
- Arithmetical laws involving cartesian product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Arithmetical laws involving dependent product types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
