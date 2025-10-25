# The universal property of the standard finite types

```agda
module univalent-combinatorics.universal-property-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universal-property-contractible-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The universal property of the standard finite types asserts that for any family
`A` of types over `Fin n`, the type `Π (i : Fin n), A i` is equivalent to the
iterated Cartesian product `A 0 × ... × A (n-1)`.

## Definitions

### Iterated cartesian products

```agda
iterated-product : {l : Level} (n : ℕ) (A : Fin n → UU l) → UU l
iterated-product zero-ℕ A = raise-unit _
iterated-product (succ-ℕ zero-ℕ) A = A (zero-Fin 0)
iterated-product (succ-ℕ (succ-ℕ n)) A =
  ( iterated-product (succ-ℕ n) (A ∘ inl-Fin (succ-ℕ n))) ×
  ( A (neg-one-Fin (succ-ℕ n)))
```

## Properties

### The dependent universal property of the standard finite types

```agda
equiv-dependent-universal-property-Fin :
  {l : Level} (n : ℕ) (A : Fin n → UU l) →
  ((i : Fin n) → A i) ≃ iterated-product n A
equiv-dependent-universal-property-Fin zero-ℕ A =
  equiv-is-contr
    ( dependent-universal-property-empty' A)
    ( is-contr-raise-unit)
equiv-dependent-universal-property-Fin (succ-ℕ zero-ℕ) A =
  equiv-dependent-universal-property-contr (zero-Fin 0) is-contr-Fin-1 A
equiv-dependent-universal-property-Fin (succ-ℕ (succ-ℕ n)) A =
  ( equiv-product
    ( equiv-dependent-universal-property-Fin (succ-ℕ n) (A ∘ inl))
    ( id-equiv)) ∘e
  ( equiv-dependent-universal-property-Maybe A)
```

### The dependent universal property of the standard 2-element type

```agda
module _
  {l : Level} (A : Fin 2 → UU l)
  where

  ev-zero-one-Fin-2 :
    ((i : Fin 2) → A i) → A (zero-Fin 1) × A (one-Fin 1)
  pr1 (ev-zero-one-Fin-2 f) = f (zero-Fin 1)
  pr2 (ev-zero-one-Fin-2 f) = f (one-Fin 1)

  map-inv-ev-zero-one-Fin-2 :
    A (zero-Fin 1) × A (one-Fin 1) → (i : Fin 2) → A i
  map-inv-ev-zero-one-Fin-2 (x , y) (inl (inr star)) = x
  map-inv-ev-zero-one-Fin-2 (x , y) (inr star) = y

  is-section-map-inv-ev-zero-one-Fin-2 :
    ev-zero-one-Fin-2 ∘ map-inv-ev-zero-one-Fin-2 ~ id
  is-section-map-inv-ev-zero-one-Fin-2 (x , y) = refl

  abstract
    is-retraction-map-inv-ev-zero-one-Fin-2 :
      map-inv-ev-zero-one-Fin-2 ∘ ev-zero-one-Fin-2 ~ id
    is-retraction-map-inv-ev-zero-one-Fin-2 f =
      eq-htpy (λ { (inl (inr star)) → refl ; (inr star) → refl})

  dependent-universal-property-Fin-2 :
    is-equiv ev-zero-one-Fin-2
  dependent-universal-property-Fin-2 =
    is-equiv-is-invertible
      map-inv-ev-zero-one-Fin-2
      is-section-map-inv-ev-zero-one-Fin-2
      is-retraction-map-inv-ev-zero-one-Fin-2

  is-equiv-map-inv-dependent-universal-proeprty-Fin-2 :
    is-equiv map-inv-ev-zero-one-Fin-2
  is-equiv-map-inv-dependent-universal-proeprty-Fin-2 =
    is-equiv-is-invertible
      ev-zero-one-Fin-2
      is-retraction-map-inv-ev-zero-one-Fin-2
      is-section-map-inv-ev-zero-one-Fin-2

  equiv-dependent-universal-property-Fin-2 :
    ((i : Fin 2) → A i) ≃ (A (zero-Fin 1) × A (one-Fin 1))
  pr1 equiv-dependent-universal-property-Fin-2 =
    ev-zero-one-Fin-2
  pr2 equiv-dependent-universal-property-Fin-2 =
    dependent-universal-property-Fin-2
```

### The universal property of the standard finite types

```agda
equiv-universal-property-Fin :
  {l : Level} (n : ℕ) {X : UU l} →
  (Fin n → X) ≃ iterated-product n (λ _ → X)
equiv-universal-property-Fin n =
  equiv-dependent-universal-property-Fin n (λ _ → _)
```

### The universal property of the standard 2-element type

```agda
module _
  {l : Level} {X : UU l}
  where

  universal-property-Fin-2 :
    is-equiv (ev-zero-one-Fin-2 (λ _ → X))
  universal-property-Fin-2 =
    dependent-universal-property-Fin-2 (λ _ → X)

  equiv-universal-property-Fin-2 :
    (Fin 2 → X) ≃ X × X
  equiv-universal-property-Fin-2 =
    equiv-dependent-universal-property-Fin-2 (λ _ → X)
```
