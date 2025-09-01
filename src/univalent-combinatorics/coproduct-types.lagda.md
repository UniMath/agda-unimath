# Coproducts of finite types

```agda
module univalent-combinatorics.coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Coproducts of finite types are finite, giving a coproduct operation on the type
`Finite-Type` of finite types.

## Properties

### The standard finite types are closed under coproducts

```agda
compute-coproduct-Fin : (k l : ℕ) → (Fin k + Fin l) ≃ Fin (k +ℕ l)
compute-coproduct-Fin k zero-ℕ = right-unit-law-coproduct (Fin k)
compute-coproduct-Fin k (succ-ℕ l) =
  ( equiv-coproduct (compute-coproduct-Fin k l) id-equiv) ∘e
  ( inv-associative-coproduct)

map-compute-coproduct-Fin : (k l : ℕ) → (Fin k + Fin l) → Fin (k +ℕ l)
map-compute-coproduct-Fin k l = map-equiv (compute-coproduct-Fin k l)

inv-compute-coproduct-Fin : (k l : ℕ) → Fin (k +ℕ l) ≃ (Fin k + Fin l)
inv-compute-coproduct-Fin k l = inv-equiv (compute-coproduct-Fin k l)

map-inv-compute-coproduct-Fin : (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-inv-compute-coproduct-Fin k l = map-equiv (inv-compute-coproduct-Fin k l)

inl-coproduct-Fin : (k l : ℕ) → Fin k → Fin (k +ℕ l)
inl-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inl

inr-coproduct-Fin : (k l : ℕ) → Fin l → Fin (k +ℕ l)
inr-coproduct-Fin k l = map-compute-coproduct-Fin k l ∘ inr

compute-inl-coproduct-Fin : (k : ℕ) → inl-coproduct-Fin k 0 ~ id
compute-inl-coproduct-Fin k x = refl

map-compute-map-inv-compute-coproduct-Fin :
  (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-compute-map-inv-compute-coproduct-Fin k zero-ℕ = inl
map-compute-map-inv-compute-coproduct-Fin k (succ-ℕ l) =
  ( map-equiv (associative-coproduct {A = Fin k} {B = Fin l})) ∘
  ( map-coproduct (map-compute-map-inv-compute-coproduct-Fin k l) id)

abstract
  compute-map-inv-compute-coproduct-Fin :
    (k l : ℕ) →
    map-inv-compute-coproduct-Fin k l ~
    map-compute-map-inv-compute-coproduct-Fin k l
  compute-map-inv-compute-coproduct-Fin k zero-ℕ x = refl
  compute-map-inv-compute-coproduct-Fin k (succ-ℕ l) x =
    ( htpy-eq
      ( distributive-map-inv-comp-equiv
        ( inv-associative-coproduct)
        ( equiv-coproduct (compute-coproduct-Fin k l) id-equiv))
      ( x)) ∙
    ( htpy-eq-equiv
      ( inv-inv-equiv associative-coproduct)
      ( map-inv-equiv-coproduct (compute-coproduct-Fin k l) id-equiv x)) ∙
    ( ap
      ( map-associative-coproduct)
      ( htpy-map-coproduct
        ( compute-map-inv-compute-coproduct-Fin k l)
        ( refl-htpy)
        ( x)))
```

### Computing the inclusion of a coproduct of standard finite types into the natural numbers

```agda
abstract
  nat-coproduct-Fin :
    (n m : ℕ) (x : Fin n + Fin m) →
    nat-Fin (n +ℕ m) (map-compute-coproduct-Fin n m x) ＝
    ind-coproduct _ (nat-Fin n) (λ i → n +ℕ (nat-Fin m i)) x
  nat-coproduct-Fin n zero-ℕ (inl x) = refl
  nat-coproduct-Fin n (succ-ℕ m) (inl x) = nat-coproduct-Fin n m (inl x)
  nat-coproduct-Fin n (succ-ℕ m) (inr (inl x)) = nat-coproduct-Fin n m (inr x)
  nat-coproduct-Fin n (succ-ℕ m) (inr (inr _)) = refl

abstract
  nat-inl-coproduct-Fin :
    (n m : ℕ) (i : Fin n) →
    nat-Fin (n +ℕ m) (inl-coproduct-Fin n m i) ＝ nat-Fin n i
  nat-inl-coproduct-Fin n m i = nat-coproduct-Fin n m (inl i)

abstract
  nat-inr-coproduct-Fin :
    (n m : ℕ) (i : Fin m) →
    nat-Fin (n +ℕ m) (inr-coproduct-Fin n m i) ＝ n +ℕ (nat-Fin m i)
  nat-inr-coproduct-Fin n m i = nat-coproduct-Fin n m (inr i)
```

### Types equipped with a count are closed under coproducts

```agda
count-coproduct :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (X + Y)
pr1 (count-coproduct (pair k e) (pair l f)) = k +ℕ l
pr2 (count-coproduct (pair k e) (pair l f)) =
  (equiv-coproduct e f) ∘e (inv-equiv (compute-coproduct-Fin k l))

abstract
  number-of-elements-count-coproduct :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    number-of-elements-count (count-coproduct e f) ＝
    (number-of-elements-count e) +ℕ (number-of-elements-count f)
  number-of-elements-count-coproduct (pair k e) (pair l f) = refl
```

### Mapping the `count-coproduct` equivalence on `inl-coproduct-Fin` is `inl` on the left count

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (cA : count A) (cB : count B)
  where

  map-equiv-count-coproduct-inl-coproduct-Fin :
    map-equiv-count (count-coproduct cA cB) ∘
    inl-coproduct-Fin
      ( number-of-elements-count cA)
      ( number-of-elements-count cB) ~
    inl ∘ map-equiv-count cA
  map-equiv-count-coproduct-inl-coproduct-Fin a =
    ap
      ( map-coproduct _ _)
      ( is-retraction-map-inv-equiv
        ( compute-coproduct-Fin
          ( number-of-elements-count cA)
          ( number-of-elements-count cB))
        ( inl a))
```

### Mapping the `count-coproduct` equivalence on `inr-coproduct-Fin` is `inr` on the right count

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (cA : count A) (cB : count B)
  where

  map-equiv-count-coproduct-inr-coproduct-Fin :
    map-equiv-count (count-coproduct cA cB) ∘
    inr-coproduct-Fin
      ( number-of-elements-count cA)
      ( number-of-elements-count cB) ~
    inr ∘ map-equiv-count cB
  map-equiv-count-coproduct-inr-coproduct-Fin b =
    ap
      ( map-coproduct _ _)
      ( is-retraction-map-inv-equiv
        ( compute-coproduct-Fin
          ( number-of-elements-count cA)
          ( number-of-elements-count cB))
        ( inr b))
```

### If both `Σ A P` and `Σ A Q` have a count, then `Σ A P + Q` have a count

```agda
count-Σ-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  count (Σ A P) → count (Σ A Q) → count (Σ A (λ x → (P x) + (Q x)))
pr1 (count-Σ-coproduct count-P count-Q) = pr1 (count-coproduct count-P count-Q)
pr2 (count-Σ-coproduct count-P count-Q) =
  ( inv-equiv left-distributive-Σ-coproduct) ∘e
  ( pr2 (count-coproduct count-P count-Q))
```

### If `X + Y` has a count, then both `X` and `Y` have a count

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  count-left-summand : count (X + Y) → count X
  count-left-summand e =
    count-equiv
      ( equiv-left-summand)
      ( count-decidable-subtype is-left-Decidable-Prop e)

  count-right-summand : count (X + Y) → count Y
  count-right-summand e =
    count-equiv
      ( equiv-right-summand)
      ( count-decidable-subtype is-right-Decidable-Prop e)
```

### If each of `A`, `B`, and `A + B` come equipped with countings, then the number of elements of `A` and of `B` add up to the number of elements of `A + B`

```agda
abstract
  double-counting-coproduct :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    ( count-A : count A) (count-B : count B) (count-C : count (A + B)) →
    Id
      ( number-of-elements-count count-C)
      ( number-of-elements-count count-A +ℕ number-of-elements-count count-B)
  double-counting-coproduct count-A count-B count-C =
    ( double-counting count-C (count-coproduct count-A count-B)) ∙
    ( number-of-elements-count-coproduct count-A count-B)

abstract
  sum-number-of-elements-coproduct :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (A + B)) →
    Id
      ( ( number-of-elements-count (count-left-summand e)) +ℕ
        ( number-of-elements-count (count-right-summand e)))
      ( number-of-elements-count e)
  sum-number-of-elements-coproduct e =
    ( inv
      ( number-of-elements-count-coproduct
        ( count-left-summand e)
        ( count-right-summand e))) ∙
    ( inv
      ( double-counting-coproduct
        ( count-left-summand e)
        ( count-right-summand e) e))
```

### Finite types are closed under coproducts

```agda
abstract
  is-finite-coproduct :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X + Y)
  is-finite-coproduct {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X + Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X + Y))
          ( is-finite-count ∘ (count-coproduct e)))

coproduct-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → Finite-Type (l1 ⊔ l2)
pr1 (coproduct-Finite-Type X Y) = (type-Finite-Type X) + (type-Finite-Type Y)
pr2 (coproduct-Finite-Type X Y) =
  is-finite-coproduct
    ( is-finite-type-Finite-Type X)
    ( is-finite-type-Finite-Type Y)

abstract
  is-finite-left-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (X + Y) →
    is-finite X
  is-finite-left-summand =
    map-trunc-Prop count-left-summand

abstract
  is-finite-right-summand :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (X + Y) →
    is-finite Y
  is-finite-right-summand =
    map-trunc-Prop count-right-summand

coproduct-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k l : ℕ) →
  Type-With-Cardinality-ℕ l1 k → Type-With-Cardinality-ℕ l2 l →
  Type-With-Cardinality-ℕ (l1 ⊔ l2) (k +ℕ l)
pr1 (coproduct-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  X + Y
pr2 (coproduct-Type-With-Cardinality-ℕ k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coproduct e1 e2 ∘e inv-equiv (compute-coproduct-Fin k l))))

coproduct-eq-is-finite :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (P : is-finite X) (Q : is-finite Y) →
    Id
      ( (number-of-elements-is-finite P) +ℕ (number-of-elements-is-finite Q))
      ( number-of-elements-is-finite (is-finite-coproduct P Q))
coproduct-eq-is-finite {X = X} {Y = Y} P Q =
  ap
    ( number-of-elements-has-finite-cardinality)
    ( all-elements-equal-has-finite-cardinality
      ( pair
        ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
        ( has-cardinality-type-Type-With-Cardinality-ℕ
          ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
          ( coproduct-Type-With-Cardinality-ℕ
            ( number-of-elements-is-finite P)
            ( number-of-elements-is-finite Q)
            ( pair X
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite P)))
            ( pair Y
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite Q))))))
      ( has-finite-cardinality-is-finite (is-finite-coproduct P Q)))
```
