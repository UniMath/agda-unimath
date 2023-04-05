# Based strong induction for the natural numbers

```agda
module elementary-number-theory.based-strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The **based strong induction principle** for the natural numbers asserts that for any natural number `k : ℕ` and any family `P` of types over the natural numbers equipped with
1. an element `p0 : P k`, and
2. a function `pS : (x : ℕ) → k ≤-ℕ x → ((y : ℕ) → k ≤-ℕ y ≤-ℕ x → P y) → P (x + 1)`
there is a function

```md
  f := based-strong-ind-ℕ k P p0 pS : (x : ℕ) → k ≤-ℕ x → P k
```

satisfying
1. `f k K ＝ p0` for any `K : k ≤-ℕ k`, and
2. `f (n + 1) N' ＝ pS n N (λ m M H → f m M)` for any `N : k ≤-ℕ n` and any `N' : k ≤-ℕ n + 1`.

## Definitions

### The based `□`-modality on families indexed by `ℕ`

```agda
based-□-≤-ℕ : {l : Level} (k : ℕ) → (ℕ → UU l) → ℕ → UU l
based-□-≤-ℕ k P n = (m : ℕ) → (k ≤-ℕ m) → (m ≤-ℕ n) → P m

η-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → P n) →
  (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
η-based-□-≤-ℕ k f n N m M p = f m M

ε-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n) →
  ((n : ℕ) → k ≤-ℕ n → P n)
ε-based-□-≤-ℕ k f n N = f n N n N (refl-leq-ℕ n)
```

## Theorem

### The base case of the based strong induction principle

```agda
base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) → P k → based-□-≤-ℕ k P k
base-based-strong-ind-ℕ zero-ℕ P p zero-ℕ M H = p
base-based-strong-ind-ℕ (succ-ℕ k) P p0 (succ-ℕ m) =
  base-based-strong-ind-ℕ k (P ∘ succ-ℕ) p0 m

eq-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p : P k)
  (s t : leq-ℕ k k) → base-based-strong-ind-ℕ k P p k s t ＝ p
eq-base-based-strong-ind-ℕ zero-ℕ P p0 M H = refl
eq-base-based-strong-ind-ℕ (succ-ℕ k) P =
  eq-base-based-strong-ind-ℕ k (P ∘ succ-ℕ)
```

### The successor case of the based strong induction principle

```agda
cases-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → P (succ-ℕ n))
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-based-strong-ind-ℕ k P pS n N f m M (inl H') = f m M H'
cases-succ-based-strong-ind-ℕ k P pS n N f .(succ-ℕ n) M (inr refl) = pS n N f

succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  ((x : ℕ) → leq-ℕ k x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) → leq-ℕ k n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)
succ-based-strong-ind-ℕ k P pS n N f m M H =
  cases-succ-based-strong-ind-ℕ k P pS n N f m M (cases-leq-succ-ℕ H)

cases-htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  (H : leq-ℕ m n) →
  cases-succ-based-strong-ind-ℕ k P pS n N f m M c ＝ f m M H
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inl p) H =
  ap (f m M) (eq-is-prop (is-prop-leq-ℕ m n))
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inr α) H =
  ex-falso (neg-succ-leq-ℕ n (concatenate-eq-leq-ℕ n (inv α) H))

htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m (succ-ℕ n)) (K : leq-ℕ m n) →
  succ-based-strong-ind-ℕ k P pS n N f m M H ＝ f m M K
htpy-succ-based-strong-ind-ℕ k P pS n N f m M H =
  cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (cases-leq-succ-ℕ H)

cases-eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (c : (leq-ℕ (succ-ℕ n) n) + (succ-ℕ n ＝ succ-ℕ n)) →
  cases-succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M c ＝ pS n N f
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inl H) =
  ex-falso (neg-succ-leq-ℕ n H)
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inr α) =
  ap ( (cases-succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M) ∘ inr)
     ( eq-is-prop' (is-set-ℕ (succ-ℕ n) (succ-ℕ n)) α refl)

eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (H : leq-ℕ (succ-ℕ n) (succ-ℕ n)) →
  succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M H ＝ pS n N f
eq-succ-based-strong-ind-ℕ k P pS n N f M H =
  cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (cases-leq-succ-ℕ H)
```

### The inductive step in the proof of based strong induction

```agda
inductive-step-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) → based-□-≤-ℕ k P k →
  ((n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)) →
  (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
inductive-step-based-strong-ind-ℕ k P =
  based-ind-ℕ k (based-□-≤-ℕ k P)

comp-base-inductive-step-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (z : based-□-≤-ℕ k P k) →
  (s : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)) →
  (K : k ≤-ℕ k) (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ k) →
  inductive-step-based-strong-ind-ℕ k P z s k K m M H ＝ z m M H
comp-base-inductive-step-based-strong-ind-ℕ k P z s K m M =
  htpy-eq
    ( htpy-eq
      ( htpy-eq
        ( comp-base-based-ind-ℕ k (based-□-≤-ℕ k P) z s K)
        ( m))
      ( M))

comp-succ-inductive-step-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (z : based-□-≤-ℕ k P k) →
  (s : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)) →
  (n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
  (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ succ-ℕ n) → 
  inductive-step-based-strong-ind-ℕ k P z s (succ-ℕ n) N' m M H ＝
  s n N (inductive-step-based-strong-ind-ℕ k P z s n N) m M H
comp-succ-inductive-step-based-strong-ind-ℕ k P z s n N N' m M =
  htpy-eq
    ( htpy-eq
      ( htpy-eq
        ( comp-succ-based-ind-ℕ k (based-□-≤-ℕ k P) z s n N N')
        ( m))
      ( M))
```

### The based strong induction principle

```agda
based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x))
  (n : ℕ) → k ≤-ℕ n → P n
based-strong-ind-ℕ k P p0 pS =
  ε-based-□-≤-ℕ k
    ( inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS))

comp-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  based-strong-ind-ℕ k P p0 pS k (refl-leq-ℕ k) ＝ p0
comp-base-based-strong-ind-ℕ k P p0 pS =
  ( comp-base-inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( refl-leq-ℕ k)
    ( k)
    ( refl-leq-ℕ k)
    ( refl-leq-ℕ k)) ∙
  ( eq-base-based-strong-ind-ℕ k P p0 (refl-leq-ℕ k) (refl-leq-ℕ k))

cases-eq-comp-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  ( n : ℕ) (N : k ≤-ℕ n) →
  ( α :
    ( m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m n) →
    inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( λ x lx f i I J →
        cases-succ-based-strong-ind-ℕ k P pS x lx f i I (cases-leq-succ-ℕ J))
      ( n)
      ( N)
      ( m)
      ( M)
      ( H) ＝
    based-strong-ind-ℕ k P p0 pS m M) →
  ( m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m (succ-ℕ n)) →
  ( K : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  ( succ-based-strong-ind-ℕ k P pS n N
    ( inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS) n N) m M H) ＝
  ( based-strong-ind-ℕ k P p0 pS m M)
cases-eq-comp-succ-based-strong-ind-ℕ k P p0 pS n N α m M H (inl K) =
  ( htpy-succ-based-strong-ind-ℕ k P pS n N
    ( inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( n)
      ( N))
    ( m)
    ( M)
    ( H)
    ( K)) ∙
  ( α m M K)
cases-eq-comp-succ-based-strong-ind-ℕ
  k P p0 pS n N α .(succ-ℕ n) M H (inr refl) =
  ( eq-succ-based-strong-ind-ℕ k P pS n N
    ( inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( n)
      ( N))
    ( M)
    ( H)) ∙
  ( ( inv
      ( eq-succ-based-strong-ind-ℕ k P pS n N _ M (refl-leq-ℕ n))) ∙
    ( inv
      ( htpy-eq
        ( htpy-eq
          ( htpy-eq
            ( comp-succ-based-ind-ℕ k
              ( based-□-≤-ℕ k P)
              ( base-based-strong-ind-ℕ k P p0)
              ( succ-based-strong-ind-ℕ k P pS)
              ( n)
              ( N)
              ( M))
            ( succ-ℕ n))
          ( M))
        ( refl-leq-ℕ n))))

eq-comp-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  ( n : ℕ) (N : k ≤-ℕ n) →
  ( m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m n) →
  ( inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( n)
    ( N)
    ( m)
    ( M)
    ( H)) ＝
  ( based-strong-ind-ℕ k P p0 pS m M)
eq-comp-succ-based-strong-ind-ℕ k P p0 pS n N m M H =
  based-ind-ℕ k
    ( λ x →
      (K : k ≤-ℕ x) (L : leq-ℕ x n) →
      inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        n N x K L ＝
      based-strong-ind-ℕ k P p0 pS x K)
    ( λ K L →
      {!!})
    ( λ x K α U V →
      {!!})
    ( m)
    ( M)
    ( M)
    ( H)
{-
  {!!} ∙
  ( cases-eq-comp-succ-based-strong-ind-ℕ k P p0 pS n N (λ x U V → {!!}) m M (preserves-leq-succ-ℕ m n H) (cases-leq-succ-ℕ (preserves-leq-succ-ℕ m n H)))
  -}
{-
eq-comp-succ-based-strong-ind-ℕ zero-ℕ P p0 pS zero-ℕ star zero-ℕ star star =
  refl
eq-comp-succ-based-strong-ind-ℕ zero-ℕ P p0 pS (succ-ℕ n) star m M H =
  cases-eq-comp-succ-based-strong-ind-ℕ 0 P p0 pS n star
    ( eq-comp-succ-based-strong-ind-ℕ 0 P p0 pS n star)
    ( m)
    ( M)
    ( H)
    ( cases-leq-succ-ℕ H)
eq-comp-succ-based-strong-ind-ℕ (succ-ℕ k) P p0 pS (succ-ℕ n) N (succ-ℕ m) M H =
  {!!} ∙
  cases-eq-comp-succ-based-strong-ind-ℕ (succ-ℕ k) P p0 pS (succ-ℕ n) N {!!} (succ-ℕ m) M (preserves-leq-succ-ℕ m n H) (cases-leq-succ-ℕ (preserves-leq-succ-ℕ m n H)) -}

comp-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  ( n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
  based-strong-ind-ℕ k P p0 pS (succ-ℕ n) N' ＝
  pS n N (λ m M H → based-strong-ind-ℕ k P p0 pS m M)
comp-succ-based-strong-ind-ℕ k P p0 pS n N N' =
  {!!}
```


