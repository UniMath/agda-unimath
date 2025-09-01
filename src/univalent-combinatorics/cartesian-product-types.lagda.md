# Cartesian products of finite types

```agda
module univalent-combinatorics.cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The cartesian product of finite types is finite. We obtain a cartesian product
operation on finite types.

### The standard finite types are closed under cartesian products

```agda
product-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (k *ℕ l)
product-Fin zero-ℕ l = left-absorption-product (Fin l)
product-Fin (succ-ℕ k) l =
  ( ( compute-coproduct-Fin (k *ℕ l) l) ∘e
    ( equiv-coproduct (product-Fin k l) left-unit-law-product)) ∘e
  ( right-distributive-product-coproduct (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (k *ℕ l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (product-Fin k l)
```

```agda
count-product :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-product (pair k e) (pair l f)) = k *ℕ l
pr2 (count-product (pair k e) (pair l f)) =
  (equiv-product e f) ∘e (inv-equiv (product-Fin k l))

abstract
  number-of-elements-count-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    number-of-elements-count (count-product count-A count-B) ＝
    number-of-elements-count count-A *ℕ number-of-elements-count count-B
  number-of-elements-count-product (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → pr2 t ＝ y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-product) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-torsorial-Id' y) is-contr-unit))) ∘e
  ( associative-Σ X (λ x → Y) (λ t → pr2 t ＝ y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-product e) x
```

```agda
abstract
  product-number-of-elements-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-AB : count (A × B)) →
    (a : A) (b : B) →
    Id
      ( ( number-of-elements-count (count-left-factor count-AB b)) *ℕ
        ( number-of-elements-count (count-right-factor count-AB a)))
      ( number-of-elements-count count-AB)
  product-number-of-elements-product count-AB a b =
    ( inv
      ( number-of-elements-count-product
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))) ∙
    ( double-counting
      ( count-product
        ( count-left-factor count-AB b)
        ( count-right-factor count-AB a))
      ( count-AB))
```

```agda
abstract
  is-finite-product :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-product {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X × Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X × Y))
          ( is-finite-count ∘ (count-product e)))

product-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (product-Finite-Type X Y) = (type-Finite-Type X) × (type-Finite-Type Y)
pr2 (product-Finite-Type X Y) =
  is-finite-product
    ( is-finite-type-Finite-Type X)
    ( is-finite-type-Finite-Type Y)

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y =
    map-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    map-trunc-Prop (λ e → count-right-factor e x) f

product-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k l : ℕ) →
  Type-With-Cardinality-ℕ l1 k → Type-With-Cardinality-ℕ l2 l →
  Type-With-Cardinality-ℕ (l1 ⊔ l2) (k *ℕ l)
pr1 (product-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) = X × Y
pr2 (product-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k *ℕ l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k *ℕ l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-product e1 e2 ∘e inv-equiv (product-Fin k l))))
```
