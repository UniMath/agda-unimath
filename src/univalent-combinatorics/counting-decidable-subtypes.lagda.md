# Counting the elements of decidable subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-decidable-subtypes where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using (zero-Fin; Fin)

open import foundation.contractible-types using (equiv-is-contr; is-contr-Σ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (map-equiv; _≃_; id-equiv)
open import foundation.fibers-of-maps using (equiv-fib-pr1)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.subtypes using (type-subtype)
open import foundation.type-arithmetic-coproduct-types using
  ( right-distributive-Σ-coprod)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod-is-empty)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; is-empty-is-zero-number-of-elements-count; count-is-contr;
    count-is-empty; number-of-elements-count; count-equiv; count-equiv';
    is-zero-number-of-elements-count-is-empty; equiv-count; is-set-count;
    has-decidable-equality-count)
```

### Propositions have countings if and only if they are decidable

```agda
is-decidable-count :
  {l : Level} {X : UU l} → count X → is-decidable X
is-decidable-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-decidable-count (pair (succ-ℕ k) e) =
  inl (map-equiv e zero-Fin)

count-is-decidable-is-prop :
  {l : Level} {A : UU l} → is-prop A → is-decidable A → count A
count-is-decidable-is-prop H (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop H x)
count-is-decidable-is-prop H (inr f) = count-is-empty f

count-decidable-Prop :
  {l1 : Level} (P : UU-Prop l1) →
  is-decidable (type-Prop P) → count (type-Prop P)
count-decidable-Prop P (inl p) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) p)
count-decidable-Prop P (inr f) = count-is-empty f
```

### We can count the elements of an identity type of a type that has decidable equality

```agda
cases-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) → count (Id x y)
cases-count-eq d {x} {y} (inl p) =
  count-is-contr
    ( is-proof-irrelevant-is-prop (is-set-has-decidable-equality d x y) p)
cases-count-eq d (inr f) =
  count-is-empty f

count-eq :
  {l : Level} {X : UU l} → has-decidable-equality X → (x y : X) → count (Id x y)
count-eq d x y = cases-count-eq d (d x y)

cases-number-of-elements-count-eq' :
  {l : Level} {X : UU l} {x y : X} →
  is-decidable (Id x y) → ℕ
cases-number-of-elements-count-eq' (inl p) = 1
cases-number-of-elements-count-eq' (inr f) = 0

number-of-elements-count-eq' :
  {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) → ℕ
number-of-elements-count-eq' d x y =
  cases-number-of-elements-count-eq' (d x y)

cases-number-of-elements-count-eq :
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (e : is-decidable (Id x y)) →
  Id ( number-of-elements-count (cases-count-eq d e))
     ( cases-number-of-elements-count-eq' e)
cases-number-of-elements-count-eq d (inl p) = refl
cases-number-of-elements-count-eq d (inr f) = refl

abstract
  number-of-elements-count-eq :
    {l : Level} {X : UU l} (d : has-decidable-equality X) (x y : X) →
    Id ( number-of-elements-count (count-eq d x y))
      ( number-of-elements-count-eq' d x y)
  number-of-elements-count-eq d x y =
    cases-number-of-elements-count-eq d (d x y)
```

### The elements of a decidable subtype of a type equipped with a counting can be counted

```agda
count-decidable-subtype' :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  (k : ℕ) (e : Fin k ≃ X) → count (type-subtype P)
count-decidable-subtype' P d zero-ℕ e =
  count-is-empty
    ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl ∘ pr1)
count-decidable-subtype' P d (succ-ℕ k) e with d (map-equiv e (inr star))
... | inl p =
  count-equiv
    ( equiv-Σ (λ x → type-Prop (P x)) e (λ x → id-equiv))
    ( count-equiv'
      ( right-distributive-Σ-coprod
        ( Fin k)
        ( unit)
        ( λ x → type-Prop (P (map-equiv e x))))
      ( pair
        ( succ-ℕ
          ( number-of-elements-count
            ( count-decidable-subtype'
              ( λ x → P (map-equiv e (inl x)))
              ( λ x → d (map-equiv e (inl x)))
              ( k)
              ( id-equiv))))
        ( equiv-coprod
          ( equiv-count
            ( count-decidable-subtype'
              ( λ x → P (map-equiv e (inl x)))
              ( λ x → d (map-equiv e (inl x)))
              ( k)
              ( id-equiv)))
          ( equiv-is-contr
            ( is-contr-unit)
            ( is-contr-Σ
              ( is-contr-unit)
              ( star)
              ( is-proof-irrelevant-is-prop
                ( is-prop-type-Prop (P (map-equiv e (inr star))))
                ( p)))))))
... | inr f =
  count-equiv
    ( equiv-Σ (λ x → type-Prop (P x)) e (λ x → id-equiv))
    ( count-equiv'
      ( right-distributive-Σ-coprod
        ( Fin k)
        ( unit)
        ( λ x → type-Prop (P (map-equiv e x))))
      ( count-equiv'
        ( right-unit-law-coprod-is-empty
          ( Σ (Fin k) (λ x → type-Prop (P (map-equiv e (inl x)))))
          ( Σ (unit) (λ x → type-Prop (P (map-equiv e (inr x)))))
          ( λ { (pair star p) → f p}))
        ( count-decidable-subtype'
          ( λ x → P (map-equiv e (inl x)))
          ( λ x → d (map-equiv e (inl x)))
          ( k)
          ( id-equiv))))

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) →
  ((x : X) → is-decidable (type-Prop (P x))) →
  (count X) → count (Σ X (λ x → type-Prop (P x)))
count-decidable-subtype P d e =
  count-decidable-subtype' P d
    ( number-of-elements-count e)
    ( equiv-count e)
```

### If the elements of a subtype of a type equipped with a counting can be counted, then the subtype is decidable

```agda
is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : X → UU-Prop l2) → count X →
  count (type-subtype P) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P e f x =
  is-decidable-count
    ( count-equiv
      ( equiv-fib-pr1 (type-Prop ∘ P) x)
      ( count-decidable-subtype
        ( λ y → pair (Id (pr1 y) x) (is-set-count e (pr1 y) x))
        ( λ y → has-decidable-equality-count e (pr1 y) x)
        ( f)))
```
