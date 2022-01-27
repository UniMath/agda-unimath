---
title: Univalent Mathematics in Agda
---

# Truncated types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.truncated-types where

open import foundation.contractible-types using (is-contr; is-contr-is-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( is-emb-is-equiv; is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; is-equiv-map-inv-is-equiv)
open import foundation.identity-types using (Id; ap)
open import foundation.universe-levels using (Level; UU; lsuc)
open import foundation.propositions using
  ( is-prop-is-contr; is-prop; UU-Prop)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; succ-𝕋; one-𝕋; neg-one-𝕋; zero-𝕋)
```

```agda
is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)
```

## The universe of truncated types

```agda
UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where
  
  type-Truncated-Type : UU-Truncated-Type k l → UU l
  type-Truncated-Type = pr1

  abstract
    is-trunc-type-Truncated-Type :
      (A : UU-Truncated-Type k l) → is-trunc k (type-Truncated-Type A)
    is-trunc-type-Truncated-Type = pr2
```

## If a type is k-truncated, then it is (k+1)-truncated. --

```agda
abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : UU i} → is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 H = is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y = is-trunc-succ-is-trunc k (H x y)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
pr1 (truncated-type-succ-Truncated-Type k A) = type-Truncated-Type A
pr2 (truncated-type-succ-Truncated-Type k A) =
  is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A)
```

## Contractible types are k-truncated for any k.

```agda
abstract
  is-trunc-is-contr :
    {l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
  is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
  is-trunc-is-contr (succ-𝕋 k) is-contr-A =
    is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)
```

## Propositions are (k+1)-truncated for any k.

```agda
abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```

## The identity type of a k-truncated type is k-truncated

```agda
abstract
  is-trunc-Id :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id {k = neg-two-𝕋} is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id {k = succ-𝕋 k} is-trunc-A x y =
    is-trunc-succ-is-trunc k {A = Id x y} (is-trunc-A x y)

Id-Truncated-Type :
  {l : Level} {k : 𝕋} (A : UU-Truncated-Type (succ-𝕋 k) l) →
  (x y : type-Truncated-Type A) → UU-Truncated-Type k l
pr1 (Id-Truncated-Type A x y) = Id x y
pr2 (Id-Truncated-Type A x y) = is-trunc-type-Truncated-Type A x y

Id-Truncated-Type' :
  {l : Level} {k : 𝕋} (A : UU-Truncated-Type k l) →
  (x y : type-Truncated-Type A) → UU-Truncated-Type k l
pr1 (Id-Truncated-Type' A x y) = Id x y
pr2 (Id-Truncated-Type' A x y) =
  is-trunc-Id (is-trunc-type-Truncated-Type A) x y
```

## k-truncated types are closed under equivalences

```agda
abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k
      ( Id (f x) (f y))
      ( ap f {x} {y})
      ( is-emb-is-equiv is-equiv-f x y)
      ( H (f x) (f y))

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

```

## If a type embeds into a (k+1)-truncated type, then it is (k+1)-truncated

```agda
abstract
  is-trunc-is-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)
```
