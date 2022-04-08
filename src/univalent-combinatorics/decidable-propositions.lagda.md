---
title : Decidable propositions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.decidable-propositions where

open import foundation.decidable-propositions public

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using (is-decidable)
open import foundation.equivalences using (map-equiv)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; is-empty-is-zero-number-of-elements-count; count-is-contr;
    count-is-empty; number-of-elements-count)
open import univalent-combinatorics.standard-finite-types using (zero-Fin)
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


