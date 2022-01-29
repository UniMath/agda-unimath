# Truncated types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.truncated-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; is-contr-is-equiv; is-contr-Σ'; is-contr-left-factor-prod;
    is-contr-right-factor-prod; is-contr-retract-of)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( is-emb-is-equiv; is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation.equality-cartesian-product-types using
  ( Eq-prod; equiv-pair-eq)
open import foundation.equality-dependent-pair-types using (equiv-pair-eq-Σ)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; is-equiv-map-inv-is-equiv)
open import foundation.identity-types using (Id; ap; tr; refl)
open import foundation.propositions using
  ( is-prop-is-contr; is-prop; UU-Prop)
open import foundation.retractions using (_retract-of_; retract-eq)
open import foundation.truncation-levels using
  ( 𝕋; neg-two-𝕋; succ-𝕋; one-𝕋; neg-one-𝕋; zero-𝕋)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

The truncatedness of a type is a measure of the complexity of its identity types. The simplest case is a contractible type. This is the base case of the inductive definition of truncatedness for types. A type is (k+1)-truncated if its identity types are k-truncated.

## Definition

### The condition of truncatedness

```agda
is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)
```

### The universe of truncated types

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

## Properties

### If a type is k-truncated, then it is (k+1)-truncated.

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

### Contractible types are k-truncated for any k.

```agda
abstract
  is-trunc-is-contr :
    {l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
  is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
  is-trunc-is-contr (succ-𝕋 k) is-contr-A =
    is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)
```

### Propositions are (k+1)-truncated for any k.

```agda
abstract
  is-trunc-is-prop :
    { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
  is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)
```

### The identity type of a k-truncated type is k-truncated

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

### k-truncated types are closed under equivalences

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

### If a type embeds into a (k+1)-truncated type, then it is (k+1)-truncated

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

### Truncated types are closed under dependent pair types

```agda
abstract
  is-trunc-Σ :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ {k = neg-two-𝕋} is-trunc-A is-trunc-B =
    is-contr-Σ' is-trunc-A is-trunc-B
  is-trunc-Σ {k = succ-𝕋 k} {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-equiv k
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( equiv-pair-eq-Σ s t)
      ( is-trunc-Σ
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

Σ-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
pr1 (Σ-Truncated-Type A B) =
  Σ (type-Truncated-Type A) (λ a → type-Truncated-Type (B a))
pr2 (Σ-Truncated-Type A B) =
  is-trunc-Σ
    ( is-trunc-type-Truncated-Type A)
    ( λ a → is-trunc-type-Truncated-Type (B a))

fib-Truncated-Type :
  {l1 l2 : Level} {k : 𝕋} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  type-Truncated-Type B → UU-Truncated-Type k (l1 ⊔ l2)
fib-Truncated-Type A B f b =
  Σ-Truncated-Type A (λ a → Id-Truncated-Type' B (f a) b)
```

### Products of truncated types are truncated

```agda
abstract
  is-trunc-prod :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)
```

### Retracts of truncated types are truncated

```agda
abstract
  is-trunc-retract-of : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of neg-two-𝕋 (pair i (pair r H)) is-trunc-B =
    is-contr-retract-of _ (pair i (pair r H)) is-trunc-B
  is-trunc-retract-of (succ-𝕋 k) (pair i retr-i) is-trunc-B x y =
    is-trunc-retract-of k
      ( retract-eq (pair i retr-i) x y)
      ( is-trunc-B (i x) (i y))
```
