# Type arithmetic with the empty type

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.type-arithmetic-empty-type
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

We prove arithmetical laws involving the empty type.

## Laws

### Left zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr1-product-empty : empty → empty × X
  inv-pr1-product-empty ()

  is-section-inv-pr1-product-empty : (pr1 ∘ inv-pr1-product-empty) ~ id
  is-section-inv-pr1-product-empty ()

  is-retraction-inv-pr1-product-empty : (inv-pr1-product-empty ∘ pr1) ~ id
  is-retraction-inv-pr1-product-empty (pair () x)

  is-equiv-pr1-product-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-product-empty =
    is-equiv-is-invertible
      inv-pr1-product-empty
      is-section-inv-pr1-product-empty
      is-retraction-inv-pr1-product-empty

  left-zero-law-product : (empty × X) ≃ empty
  pr1 left-zero-law-product = pr1
  pr2 left-zero-law-product = is-equiv-pr1-product-empty

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (is-empty-A : is-empty A)
  where
  inv-pr1-product-is-empty : A → A × B
  inv-pr1-product-is-empty a = ex-falso (is-empty-A a)

  is-section-inv-pr1-product-is-empty : (pr1 ∘ inv-pr1-product-is-empty) ~ id
  is-section-inv-pr1-product-is-empty a = ex-falso (is-empty-A a)

  is-retraction-inv-pr1-product-is-empty : (inv-pr1-product-is-empty ∘ pr1) ~ id
  is-retraction-inv-pr1-product-is-empty (pair a b) = ex-falso (is-empty-A a)

  is-equiv-pr1-product-is-empty : is-equiv (pr1 {A = A} {B = λ a → B})
  is-equiv-pr1-product-is-empty =
    is-equiv-is-invertible
      inv-pr1-product-is-empty
      is-section-inv-pr1-product-is-empty
      is-retraction-inv-pr1-product-is-empty

  left-zero-law-product-is-empty : (A × B) ≃ A
  pr1 left-zero-law-product-is-empty = pr1
  pr2 left-zero-law-product-is-empty = is-equiv-pr1-product-is-empty
```

### Right zero law for cartesian products

```agda
module _
  {l : Level} (X : UU l)
  where

  inv-pr2-product-empty : empty → (X × empty)
  inv-pr2-product-empty ()

  is-section-inv-pr2-product-empty : (pr2 ∘ inv-pr2-product-empty) ~ id
  is-section-inv-pr2-product-empty ()

  is-retraction-inv-pr2-product-empty : (inv-pr2-product-empty ∘ pr2) ~ id
  is-retraction-inv-pr2-product-empty (pair x ())

  is-equiv-pr2-product-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-product-empty =
    is-equiv-is-invertible
      inv-pr2-product-empty
      is-section-inv-pr2-product-empty
      is-retraction-inv-pr2-product-empty

  right-zero-law-product : (X × empty) ≃ empty
  pr1 right-zero-law-product = pr2
  pr2 right-zero-law-product = is-equiv-pr2-product-empty

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (is-empty-B : is-empty B)
  where
  inv-pr2-product-is-empty : B → A × B
  inv-pr2-product-is-empty b = ex-falso (is-empty-B b)

  is-section-inv-pr2-product-is-empty : (pr2 ∘ inv-pr2-product-is-empty) ~ id
  is-section-inv-pr2-product-is-empty b = ex-falso (is-empty-B b)

  is-retraction-inv-pr2-product-is-empty : (inv-pr2-product-is-empty ∘ pr2) ~ id
  is-retraction-inv-pr2-product-is-empty (pair a b) = ex-falso (is-empty-B b)

  is-equiv-pr2-product-is-empty : is-equiv (pr2 {A = A} {B = λ a → B})
  is-equiv-pr2-product-is-empty =
    is-equiv-is-invertible
      inv-pr2-product-is-empty
      is-section-inv-pr2-product-is-empty
      is-retraction-inv-pr2-product-is-empty

  right-zero-law-product-is-empty : (A × B) ≃ B
  pr1 right-zero-law-product-is-empty = pr2
  pr2 right-zero-law-product-is-empty = is-equiv-pr2-product-is-empty
```

### Right absorption law for dependent pair types and for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-right-absorption-Σ : Σ A (λ x → empty) → empty
  map-right-absorption-Σ (pair x ())

  is-equiv-map-right-absorption-Σ : is-equiv map-right-absorption-Σ
  is-equiv-map-right-absorption-Σ = is-equiv-is-empty' map-right-absorption-Σ

  right-absorption-Σ : Σ A (λ x → empty) ≃ empty
  right-absorption-Σ =
    pair map-right-absorption-Σ is-equiv-map-right-absorption-Σ
```

### Left absorption law for dependent pair types

```agda
module _
  {l : Level} (A : empty → UU l)
  where

  map-left-absorption-Σ : Σ empty A → empty
  map-left-absorption-Σ = pr1

  is-equiv-map-left-absorption-Σ : is-equiv map-left-absorption-Σ
  is-equiv-map-left-absorption-Σ =
    is-equiv-is-empty' map-left-absorption-Σ

  left-absorption-Σ : Σ empty A ≃ empty
  pr1 left-absorption-Σ = map-left-absorption-Σ
  pr2 left-absorption-Σ = is-equiv-map-left-absorption-Σ
```

### Right absorption law for cartesian product types

```agda
module _
  {l : Level} {A : UU l}
  where

  map-right-absorption-product : A × empty → empty
  map-right-absorption-product = map-right-absorption-Σ A

  is-equiv-map-right-absorption-product : is-equiv map-right-absorption-product
  is-equiv-map-right-absorption-product = is-equiv-map-right-absorption-Σ A

  right-absorption-product : (A × empty) ≃ empty
  right-absorption-product = right-absorption-Σ A

is-empty-right-factor-is-empty-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → A → is-empty B
is-empty-right-factor-is-empty-product f a b = f (pair a b)
```

### Left absorption law for cartesian products

```agda
module _
  {l : Level} (A : UU l)
  where

  map-left-absorption-product : empty × A → empty
  map-left-absorption-product = map-left-absorption-Σ (λ x → A)

  is-equiv-map-left-absorption-product : is-equiv map-left-absorption-product
  is-equiv-map-left-absorption-product =
    is-equiv-map-left-absorption-Σ (λ x → A)

  left-absorption-product : (empty × A) ≃ empty
  left-absorption-product = left-absorption-Σ (λ x → A)

is-empty-left-factor-is-empty-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty (A × B) → B → is-empty A
is-empty-left-factor-is-empty-product f b a = f (pair a b)
```

### Left unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A)
  where

  map-left-unit-law-coproduct-is-empty : A + B → B
  map-left-unit-law-coproduct-is-empty (inl a) = ex-falso (H a)
  map-left-unit-law-coproduct-is-empty (inr b) = b

  map-inv-left-unit-law-coproduct-is-empty : B → A + B
  map-inv-left-unit-law-coproduct-is-empty = inr

  is-section-map-inv-left-unit-law-coproduct-is-empty :
    ( map-left-unit-law-coproduct-is-empty ∘
      map-inv-left-unit-law-coproduct-is-empty) ~ id
  is-section-map-inv-left-unit-law-coproduct-is-empty = refl-htpy

  is-retraction-map-inv-left-unit-law-coproduct-is-empty :
    ( map-inv-left-unit-law-coproduct-is-empty ∘
      map-left-unit-law-coproduct-is-empty) ~ id
  is-retraction-map-inv-left-unit-law-coproduct-is-empty (inl a) =
    ex-falso (H a)
  is-retraction-map-inv-left-unit-law-coproduct-is-empty (inr b) = refl

  is-equiv-map-left-unit-law-coproduct-is-empty :
    is-equiv map-left-unit-law-coproduct-is-empty
  is-equiv-map-left-unit-law-coproduct-is-empty =
    is-equiv-is-invertible
      map-inv-left-unit-law-coproduct-is-empty
      is-section-map-inv-left-unit-law-coproduct-is-empty
      is-retraction-map-inv-left-unit-law-coproduct-is-empty

  left-unit-law-coproduct-is-empty : (A + B) ≃ B
  pr1 left-unit-law-coproduct-is-empty = map-left-unit-law-coproduct-is-empty
  pr2 left-unit-law-coproduct-is-empty =
    is-equiv-map-left-unit-law-coproduct-is-empty

  is-equiv-inr-is-empty :
    is-equiv inr
  is-equiv-inr-is-empty =
    is-equiv-is-invertible
      ( map-left-unit-law-coproduct-is-empty)
      ( is-retraction-map-inv-left-unit-law-coproduct-is-empty)
      ( is-section-map-inv-left-unit-law-coproduct-is-empty)

  inv-left-unit-law-coproduct-is-empty : B ≃ (A + B)
  pr1 inv-left-unit-law-coproduct-is-empty =
    map-inv-left-unit-law-coproduct-is-empty
  pr2 inv-left-unit-law-coproduct-is-empty = is-equiv-inr-is-empty

  is-contr-map-left-unit-law-coproduct-is-empty :
    is-contr-map map-left-unit-law-coproduct-is-empty
  is-contr-map-left-unit-law-coproduct-is-empty =
    is-contr-map-is-equiv is-equiv-map-left-unit-law-coproduct-is-empty

  is-contr-map-inr-is-empty :
    is-contr-map map-inv-left-unit-law-coproduct-is-empty
  is-contr-map-inr-is-empty = is-contr-map-is-equiv is-equiv-inr-is-empty

  is-right-coproduct-is-empty : (x : A + B) → Σ B (λ b → inr b ＝ x)
  is-right-coproduct-is-empty x = center (is-contr-map-inr-is-empty x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-empty-left-summand-is-equiv : is-equiv (inr {A = A} {B = B}) → is-empty A
  is-empty-left-summand-is-equiv H a =
    neq-inr-inl (is-section-map-inv-is-equiv H (inl a))

module _
  {l : Level} (B : UU l)
  where

  map-left-unit-law-coproduct : empty + B → B
  map-left-unit-law-coproduct = map-left-unit-law-coproduct-is-empty empty B id

  map-inv-left-unit-law-coproduct : B → empty + B
  map-inv-left-unit-law-coproduct = inr

  is-section-map-inv-left-unit-law-coproduct :
    ( map-left-unit-law-coproduct ∘ map-inv-left-unit-law-coproduct) ~ id
  is-section-map-inv-left-unit-law-coproduct =
    is-section-map-inv-left-unit-law-coproduct-is-empty empty B id

  is-retraction-map-inv-left-unit-law-coproduct :
    ( map-inv-left-unit-law-coproduct ∘ map-left-unit-law-coproduct) ~ id
  is-retraction-map-inv-left-unit-law-coproduct =
    is-retraction-map-inv-left-unit-law-coproduct-is-empty empty B id

  is-equiv-map-left-unit-law-coproduct : is-equiv map-left-unit-law-coproduct
  is-equiv-map-left-unit-law-coproduct =
    is-equiv-map-left-unit-law-coproduct-is-empty empty B id

  left-unit-law-coproduct : (empty + B) ≃ B
  left-unit-law-coproduct = left-unit-law-coproduct-is-empty empty B id

  inv-left-unit-law-coproduct : B ≃ (empty + B)
  inv-left-unit-law-coproduct = inv-left-unit-law-coproduct-is-empty empty B id
```

### Right unit law for coproducts

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B)
  where

  map-right-unit-law-coproduct-is-empty : A + B → A
  map-right-unit-law-coproduct-is-empty (inl a) = a
  map-right-unit-law-coproduct-is-empty (inr b) = ex-falso (H b)

  map-inv-right-unit-law-coproduct-is-empty : A → A + B
  map-inv-right-unit-law-coproduct-is-empty = inl

  is-section-map-inv-right-unit-law-coproduct-is-empty :
    ( map-right-unit-law-coproduct-is-empty ∘
      map-inv-right-unit-law-coproduct-is-empty) ~ id
  is-section-map-inv-right-unit-law-coproduct-is-empty a = refl

  is-retraction-map-inv-right-unit-law-coproduct-is-empty :
    ( map-inv-right-unit-law-coproduct-is-empty ∘
      map-right-unit-law-coproduct-is-empty) ~ id
  is-retraction-map-inv-right-unit-law-coproduct-is-empty (inl a) = refl
  is-retraction-map-inv-right-unit-law-coproduct-is-empty (inr b) =
    ex-falso (H b)

  is-equiv-map-right-unit-law-coproduct-is-empty :
    is-equiv map-right-unit-law-coproduct-is-empty
  is-equiv-map-right-unit-law-coproduct-is-empty =
    is-equiv-is-invertible
      map-inv-right-unit-law-coproduct-is-empty
      is-section-map-inv-right-unit-law-coproduct-is-empty
      is-retraction-map-inv-right-unit-law-coproduct-is-empty

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty =
    is-equiv-is-invertible
      ( map-right-unit-law-coproduct-is-empty)
      ( is-retraction-map-inv-right-unit-law-coproduct-is-empty)
      ( is-section-map-inv-right-unit-law-coproduct-is-empty)

  right-unit-law-coproduct-is-empty : (A + B) ≃ A
  pr1 right-unit-law-coproduct-is-empty = map-right-unit-law-coproduct-is-empty
  pr2 right-unit-law-coproduct-is-empty =
    is-equiv-map-right-unit-law-coproduct-is-empty

  inv-right-unit-law-coproduct-is-empty : A ≃ (A + B)
  pr1 inv-right-unit-law-coproduct-is-empty = inl
  pr2 inv-right-unit-law-coproduct-is-empty = is-equiv-inl-is-empty

  is-contr-map-right-unit-law-coproduct-is-empty :
    is-contr-map map-right-unit-law-coproduct-is-empty
  is-contr-map-right-unit-law-coproduct-is-empty =
    is-contr-map-is-equiv is-equiv-map-right-unit-law-coproduct-is-empty

  is-contr-map-inl-is-empty : is-contr-map inl
  is-contr-map-inl-is-empty = is-contr-map-is-equiv is-equiv-inl-is-empty

  is-left-coproduct-is-empty :
    (x : A + B) → Σ A (λ a → inl a ＝ x)
  is-left-coproduct-is-empty x = center (is-contr-map-inl-is-empty x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-empty-right-summand-is-equiv : is-equiv (inl {A = A} {B = B}) → is-empty B
  is-empty-right-summand-is-equiv H b =
    neq-inl-inr (is-section-map-inv-is-equiv H (inr b))

module _
  {l : Level} (A : UU l)
  where

  map-right-unit-law-coproduct : A + empty → A
  map-right-unit-law-coproduct =
    map-right-unit-law-coproduct-is-empty A empty id

  map-inv-right-unit-law-coproduct : A → A + empty
  map-inv-right-unit-law-coproduct = inl

  is-section-map-inv-right-unit-law-coproduct :
    ( map-right-unit-law-coproduct ∘ map-inv-right-unit-law-coproduct) ~ id
  is-section-map-inv-right-unit-law-coproduct =
    is-section-map-inv-right-unit-law-coproduct-is-empty A empty id

  is-retraction-map-inv-right-unit-law-coproduct :
    ( map-inv-right-unit-law-coproduct ∘ map-right-unit-law-coproduct) ~ id
  is-retraction-map-inv-right-unit-law-coproduct =
    is-retraction-map-inv-right-unit-law-coproduct-is-empty A empty id

  is-equiv-map-right-unit-law-coproduct : is-equiv map-right-unit-law-coproduct
  is-equiv-map-right-unit-law-coproduct =
    is-equiv-map-right-unit-law-coproduct-is-empty A empty id

  right-unit-law-coproduct : (A + empty) ≃ A
  right-unit-law-coproduct = right-unit-law-coproduct-is-empty A empty id

  inv-right-unit-law-coproduct : A ≃ (A + empty)
  inv-right-unit-law-coproduct =
    inv-right-unit-law-coproduct-is-empty A empty id
```

## See also

- In
  [`foundation.universal-property-empty-type`](foundation.universal-property-empty-type.md)
  we show that `empty` is the initial type, which can be considered a _left zero
  law for function types_ (`(empty → A) ≃ unit`).
