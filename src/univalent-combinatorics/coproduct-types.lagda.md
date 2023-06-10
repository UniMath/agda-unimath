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
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
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
coprod-Fin :
  (k l : ℕ) → (Fin k + Fin l) ≃ Fin (k +ℕ l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) id-equiv) ∘e inv-associative-coprod

map-coprod-Fin :
  (k l : ℕ) → (Fin k + Fin l) → Fin (k +ℕ l)
map-coprod-Fin k l = map-equiv (coprod-Fin k l)

Fin-add-ℕ :
  (k l : ℕ) → Fin (k +ℕ l) ≃ (Fin k + Fin l)
Fin-add-ℕ k l = inv-equiv (coprod-Fin k l)

inl-coprod-Fin :
  (k l : ℕ) → Fin k → Fin (k +ℕ l)
inl-coprod-Fin k l = map-coprod-Fin k l ∘ inl

inr-coprod-Fin :
  (k l : ℕ) → Fin l → Fin (k +ℕ l)
inr-coprod-Fin k l = map-coprod-Fin k l ∘ inr

compute-inl-coprod-Fin :
  (k : ℕ) → inl-coprod-Fin k 0 ~ id
compute-inl-coprod-Fin k x = refl
```

### Inclusion of `coprod-Fin` into the natural numbers

```agda
nat-coprod-Fin :
  (n m : ℕ) → (x : Fin n + Fin m) →
  nat-Fin (n +ℕ m) (map-coprod-Fin n m x) ＝
  ind-coprod _ (nat-Fin n) (λ i → n +ℕ (nat-Fin m i)) x
nat-coprod-Fin n zero-ℕ (inl x) = refl
nat-coprod-Fin n (succ-ℕ m) (inl x) = nat-coprod-Fin n m (inl x)
nat-coprod-Fin n (succ-ℕ m) (inr (inl x)) = nat-coprod-Fin n m (inr x)
nat-coprod-Fin n (succ-ℕ m) (inr (inr star)) = refl

nat-inl-coprod-Fin :
  (n m : ℕ) (i : Fin n) →
  nat-Fin (n +ℕ m) (inl-coprod-Fin n m i) ＝ nat-Fin n i
nat-inl-coprod-Fin n m i = nat-coprod-Fin n m (inl i)

nat-inr-coprod-Fin :
  (n m : ℕ) (i : Fin m) →
  nat-Fin (n +ℕ m) (inr-coprod-Fin n m i) ＝ n +ℕ (nat-Fin m i)
nat-inr-coprod-Fin n m i = nat-coprod-Fin n m (inr i)
```

### Types equipped with a count are closed under coproducts

```agda
count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (X + Y)
pr1 (count-coprod (pair k e) (pair l f)) = k +ℕ l
pr2 (count-coprod (pair k e) (pair l f)) =
  (equiv-coprod e f) ∘e (inv-equiv (coprod-Fin k l))

abstract
  number-of-elements-count-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coprod e f))
      ( (number-of-elements-count e) +ℕ (number-of-elements-count f))
  number-of-elements-count-coprod (pair k e) (pair l f) = refl
```

### If both `Σ A P` and `Σ A Q` have a count, then `Σ A P + Q` have a count

```agda
count-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  count (Σ A P) → count (Σ A Q) → count (Σ A (λ x → (P x) + (Q x)))
pr1 (count-Σ-coprod count-P count-Q) = pr1 (count-coprod count-P count-Q)
pr2 (count-Σ-coprod count-P count-Q) =
  ( inv-equiv (left-distributive-Σ-coprod _ _ _)) ∘e
  ( pr2 (count-coprod count-P count-Q))
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
  double-counting-coprod :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    ( count-A : count A) (count-B : count B) (count-C : count (A + B)) →
    Id
      ( number-of-elements-count count-C)
      ( number-of-elements-count count-A +ℕ number-of-elements-count count-B)
  double-counting-coprod count-A count-B count-C =
    ( double-counting count-C (count-coprod count-A count-B)) ∙
    ( number-of-elements-count-coprod count-A count-B)

abstract
  sum-number-of-elements-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (A + B)) →
    Id
      ( ( number-of-elements-count (count-left-summand e)) +ℕ
        ( number-of-elements-count (count-right-summand e)))
      ( number-of-elements-count e)
  sum-number-of-elements-coprod e =
    ( inv
      ( number-of-elements-count-coprod
        ( count-left-summand e)
        ( count-right-summand e))) ∙
    ( inv
      ( double-counting-coprod
        ( count-left-summand e)
        ( count-right-summand e) e))
```

### Finite types are closed under coproducts

```agda
abstract
  is-finite-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X + Y)
  is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X + Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X + Y))
          ( is-finite-count ∘ (count-coprod e)))

coprod-𝔽 : {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (l1 ⊔ l2)
pr1 (coprod-𝔽 X Y) = (type-𝔽 X) + (type-𝔽 Y)
pr2 (coprod-𝔽 X Y) = is-finite-coprod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

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

coprod-UU-Fin :
  {l1 l2 : Level} (k l : ℕ) → UU-Fin l1 k → UU-Fin l2 l →
  UU-Fin (l1 ⊔ l2) (k +ℕ l)
pr1 (coprod-UU-Fin {l1} {l2} k l (pair X H) (pair Y K)) = X + Y
pr2 (coprod-UU-Fin {l1} {l2} k l (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (k +ℕ l)) (X + Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coprod e1 e2 ∘e inv-equiv (coprod-Fin k l))))

coprod-eq-is-finite :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (P : is-finite X) (Q : is-finite Y) →
    Id
      ( (number-of-elements-is-finite P) +ℕ (number-of-elements-is-finite Q))
      ( number-of-elements-is-finite (is-finite-coprod P Q))
coprod-eq-is-finite {X = X} {Y = Y} P Q =
  ap
    ( number-of-elements-has-finite-cardinality)
    ( all-elements-equal-has-finite-cardinality
      ( pair
        ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
        ( has-cardinality-type-UU-Fin
          ( number-of-elements-is-finite P +ℕ number-of-elements-is-finite Q)
          ( coprod-UU-Fin
            ( number-of-elements-is-finite P)
            ( number-of-elements-is-finite Q)
            ( pair X
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite P)))
            ( pair Y
              ( mere-equiv-has-finite-cardinality
                ( has-finite-cardinality-is-finite Q))))))
      ( has-finite-cardinality-is-finite (is-finite-coprod P Q)))
```
