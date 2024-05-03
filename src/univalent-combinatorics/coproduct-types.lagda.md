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
open import foundation.equivalences
open import foundation.equivalence-extensionality
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
𝔽 of finite types.

## Properties

### The standard finite types are closed under coproducts

```agda
coproduct-Fin :
  (k l : ℕ) → (Fin k + Fin l) ≃ Fin (k +ℕ l)
coproduct-Fin k zero-ℕ = right-unit-law-coproduct (Fin k)
coproduct-Fin k (succ-ℕ l) =
  (equiv-coproduct (coproduct-Fin k l) id-equiv) ∘e inv-associative-coproduct

map-coproduct-Fin :
  (k l : ℕ) → (Fin k + Fin l) → Fin (k +ℕ l)
map-coproduct-Fin k l = map-equiv (coproduct-Fin k l)

Fin-add-ℕ :
  (k l : ℕ) → Fin (k +ℕ l) ≃ (Fin k + Fin l)
Fin-add-ℕ k l = inv-equiv (coproduct-Fin k l)

inl-coproduct-Fin :
  (k l : ℕ) → Fin k → Fin (k +ℕ l)
inl-coproduct-Fin k l = map-coproduct-Fin k l ∘ inl

inr-coproduct-Fin :
  (k l : ℕ) → Fin l → Fin (k +ℕ l)
inr-coproduct-Fin k l = map-coproduct-Fin k l ∘ inr

compute-inl-coproduct-Fin :
  (k : ℕ) → inl-coproduct-Fin k 0 ~ id
compute-inl-coproduct-Fin k x = refl

map-Fin-add-ℕ :
  (k l : ℕ) → Fin (k +ℕ l) → Fin k + Fin l
map-Fin-add-ℕ k zero-ℕ = inl
map-Fin-add-ℕ k (succ-ℕ l) =
  ( map-equiv (associative-coproduct {A = Fin k} {B = Fin l})) ∘
  ( map-coproduct (map-Fin-add-ℕ k l) id)

compute-map-Fin-add-ℕ :
  (k l : ℕ) → map-equiv (Fin-add-ℕ k l) ~ map-Fin-add-ℕ k l
compute-map-Fin-add-ℕ k zero-ℕ x = refl
compute-map-Fin-add-ℕ k (succ-ℕ l) x =
  ( htpy-eq
    ( distributive-map-inv-comp-equiv
      ( inv-associative-coproduct)
      ( equiv-coproduct (coproduct-Fin k l) id-equiv))
    ( x)) ∙
  ( htpy-eq-equiv
    ( inv-inv-equiv associative-coproduct)
    ( map-inv-equiv (equiv-coproduct (coproduct-Fin k l) id-equiv) x)) ∙
  ( ap
    ( map-associative-coproduct)
    ( ( compute-map-inv-equiv-coproduct (coproduct-Fin k l) (id-equiv) x) ∙
    ( htpy-map-coproduct (compute-map-Fin-add-ℕ k l) refl-htpy x)))
```

### Inclusion of `coproduct-Fin` into the natural numbers

```agda
nat-coproduct-Fin :
  (n m : ℕ) → (x : Fin n + Fin m) →
  nat-Fin (n +ℕ m) (map-coproduct-Fin n m x) ＝
  ind-coproduct _ (nat-Fin n) (λ i → n +ℕ (nat-Fin m i)) x
nat-coproduct-Fin n zero-ℕ (inl x) = refl
nat-coproduct-Fin n (succ-ℕ m) (inl x) = nat-coproduct-Fin n m (inl x)
nat-coproduct-Fin n (succ-ℕ m) (inr (inl x)) = nat-coproduct-Fin n m (inr x)
nat-coproduct-Fin n (succ-ℕ m) (inr (inr _)) = refl

nat-inl-coproduct-Fin :
  (n m : ℕ) (i : Fin n) →
  nat-Fin (n +ℕ m) (inl-coproduct-Fin n m i) ＝ nat-Fin n i
nat-inl-coproduct-Fin n m i = nat-coproduct-Fin n m (inl i)

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
  (equiv-coproduct e f) ∘e (inv-equiv (coproduct-Fin k l))

abstract
  number-of-elements-count-coproduct :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coproduct e f))
      ( (number-of-elements-count e) +ℕ (number-of-elements-count f))
  number-of-elements-count-coproduct (pair k e) (pair l f) = refl
```

### If both `Σ A P` and `Σ A Q` have a count, then `Σ A P + Q` have a count

```agda
count-Σ-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  count (Σ A P) → count (Σ A Q) → count (Σ A (λ x → (P x) + (Q x)))
pr1 (count-Σ-coproduct count-P count-Q) = pr1 (count-coproduct count-P count-Q)
pr2 (count-Σ-coproduct count-P count-Q) =
  ( inv-equiv (left-distributive-Σ-coproduct _ _ _)) ∘e
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

coproduct-𝔽 : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (coproduct-𝔽 X Y) = (type-𝔽 X) + (type-𝔽 Y)
pr2 (coproduct-𝔽 X Y) =
  is-finite-coproduct (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

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

coproduct-UU-Fin :
  {l1 l2 : Level} (k l : ℕ) → UU-Fin l1 k → UU-Fin l2 l →
  UU-Fin (l1 ⊔ l2) (k +ℕ l)
pr1 (coproduct-UU-Fin {l1} {l2} k l (pair X H) (pair Y K)) = X + Y
pr2 (coproduct-UU-Fin {l1} {l2} k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coproduct e1 e2 ∘e inv-equiv (coproduct-Fin k l))))

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
        ( has-cardinality-type-UU-Fin
          ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
          ( coproduct-UU-Fin
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
