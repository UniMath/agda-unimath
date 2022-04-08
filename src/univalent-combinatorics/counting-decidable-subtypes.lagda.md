---
title: Counting the elements of decidable subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-decidable-subtypes where

open import foundation.decidable-subtypes public

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.contractible-types using (equiv-is-contr; is-contr-Σ)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-embeddings using
  ( _↪d_; map-decidable-emb; decidable-subtype-decidable-emb)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.equivalences using (map-equiv; _≃_; id-equiv)
open import foundation.fibers-of-maps using
  ( equiv-fib-pr1; equiv-total-fib; fib)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-dependent-pair-types using (equiv-Σ)
open import foundation.identity-types using (Id; refl)
open import foundation.propositional-maps using (is-prop-map-emb)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.subtypes using (subtype; type-subtype)
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
open import univalent-combinatorics.decidable-propositions using
  ( is-decidable-count)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-equiv')
open import univalent-combinatorics.standard-finite-types using (zero-Fin; Fin)
```

## Properties

### The elements of a decidable subtype of a type equipped with a counting can be counted

```agda
count-decidable-subtype' :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
  (k : ℕ) (e : Fin k ≃ X) → count (type-decidable-subtype P)
count-decidable-subtype' P zero-ℕ e =
  count-is-empty
    ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl ∘ pr1)
count-decidable-subtype' P (succ-ℕ k) e
  with is-decidable-subtype-subtype-decidable-subtype P (map-equiv e (inr star))
... | inl p =
  count-equiv
    ( equiv-Σ (type-prop-decidable-subtype P) e (λ x → id-equiv))
    ( count-equiv'
      ( right-distributive-Σ-coprod
        ( Fin k)
        ( unit)
        ( λ x → type-prop-decidable-subtype P (map-equiv e x)))
      ( pair
        ( succ-ℕ
          ( number-of-elements-count
            ( count-decidable-subtype'
              ( λ x → P (map-equiv e (inl x)))
              ( k)
              ( id-equiv))))
        ( equiv-coprod
          ( equiv-count
            ( count-decidable-subtype'
              ( λ x → P (map-equiv e (inl x)))
              ( k)
              ( id-equiv)))
          ( equiv-is-contr
            ( is-contr-unit)
            ( is-contr-Σ
              ( is-contr-unit)
              ( star)
              ( is-proof-irrelevant-is-prop
                ( is-prop-type-prop-decidable-subtype P
                  ( map-equiv e (inr star)))
                ( p)))))))
... | inr f =
  count-equiv
    ( equiv-Σ (type-prop-decidable-subtype P) e (λ x → id-equiv))
    ( count-equiv'
      ( right-distributive-Σ-coprod
        ( Fin k)
        ( unit)
        ( λ x → type-prop-decidable-subtype P (map-equiv e x)))
      ( count-equiv'
        ( right-unit-law-coprod-is-empty
          ( Σ ( Fin k)
              ( λ x → type-prop-decidable-subtype P (map-equiv e (inl x))))
          ( Σ ( unit)
              ( λ x → type-prop-decidable-subtype P (map-equiv e (inr x))))
          ( λ { (pair star p) → f p}))
        ( count-decidable-subtype'
          ( λ x → P (map-equiv e (inl x)))
          ( k)
          ( id-equiv))))

count-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} (P : decidable-subtype l2 X) →
  (count X) → count (type-decidable-subtype P)
count-decidable-subtype P e =
  count-decidable-subtype' P
    ( number-of-elements-count e)
    ( equiv-count e)
```

### The elements in the domain of a decidable embedding can be counted if the elements of the codomain can be counted

```agda
count-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪d Y) → count Y → count X
count-decidable-emb f e =
  count-equiv
    ( equiv-total-fib (map-decidable-emb f))
    ( count-decidable-subtype (decidable-subtype-decidable-emb f) e)
```

### If the elements of a subtype of a type equipped with a counting can be counted, then the subtype is decidable

```agda
is-decidable-count-subtype :
  {l1 l2 : Level} {X : UU l1} (P : subtype l2 X) → count X →
  count (type-subtype P) → (x : X) → is-decidable (type-Prop (P x))
is-decidable-count-subtype P e f x =
  is-decidable-count
    ( count-equiv
      ( equiv-fib-pr1 (type-Prop ∘ P) x)
      ( count-decidable-subtype
        ( λ y →
          pair
            ( Id (pr1 y) x)
            ( pair
              ( is-set-count e (pr1 y) x)
              ( has-decidable-equality-count e (pr1 y) x)))
        ( f)))
```

### If a subtype of a type equipped with a counting is finite, then its elements can be counted

```agda
count-type-subtype-is-finite-type-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : subtype l2 A) →
  is-finite (type-subtype P) → count (type-subtype P)
count-type-subtype-is-finite-type-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype
    ( λ x → pair (type-Prop (P x)) (pair (is-prop-type-Prop (P x)) (d x)))
    ( e)
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-subtype P e g x)
```

### For any embedding `B ↪ A` into a type `A` equipped with a counting, if `B` is finite then its elements can be counted

```agda
count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-type-subtype-is-finite-type-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))
```
