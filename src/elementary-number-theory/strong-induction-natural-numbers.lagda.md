# The strong induction principle for the natural numbers

```agda
module elementary-number-theory.strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
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
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The strong induction principle allows one to assume in the inductive step that the inductive hypothesis is satisfied at all smaller values.

## Definition

### A `□`-modality on families indexed by `ℕ`

```agda
□-≤-ℕ : {l : Level} → (ℕ → UU l) → ℕ → UU l
□-≤-ℕ P n = (m : ℕ) → (m ≤-ℕ n) → P m

η-□-≤-ℕ : {l : Level} {P : ℕ → UU l} → ((n : ℕ) → P n) → (n : ℕ) → □-≤-ℕ P n
η-□-≤-ℕ f n m p = f m

ε-□-≤-ℕ :
  {l : Level} {P : ℕ → UU l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ f n = f n n (refl-leq-ℕ n)
```

### The base case of the strong induction principle

```agda
zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  zero-strong-ind-ℕ P p0 zero-ℕ t ＝ p0
eq-zero-strong-ind-ℕ P p0 t = refl
```

### Preparing induction

```agda
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p)

cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : (leq-ℕ m k) + (m ＝ succ-ℕ k)) →
  (q : leq-ℕ m k) →
  ( cases-succ-strong-ind-ℕ P pS k H m c) ＝
  ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (eq-is-prop (is-prop-leq-ℕ m k))
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso (neg-succ-leq-ℕ k (leq-eq-left-ℕ α k q))

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  ( succ-strong-ind-ℕ P pS k H m p) ＝
  ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p) q

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : (leq-ℕ (succ-ℕ k) k) + (succ-ℕ k ＝ succ-ℕ k)) →
  ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c)) ＝
  ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso (neg-succ-leq-ℕ k p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
     ( eq-is-prop' (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p)) ＝
  ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (cases-leq-succ-ℕ p)
```

### The inductive step

```agda
induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ P q0 qS zero-ℕ = q0
induction-strong-ind-ℕ P q0 qS (succ-ℕ n) =
  qS n (induction-strong-ind-ℕ P q0 qS n)

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (q0 : □-≤-ℕ P zero-ℕ) →
  (qS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  ( induction-strong-ind-ℕ P q0 qS (succ-ℕ n)) ＝
  ( qS n (induction-strong-ind-ℕ P q0 qS n))
computation-succ-strong-ind-ℕ P q0 qS n = refl
```

### We condluce the strong induction principle

```agda
strong-ind-ℕ :
  {l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ P p0 pS =
  ε-□-≤-ℕ
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

comp-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  strong-ind-ℕ P p0 pS zero-ℕ ＝ p0
comp-zero-strong-ind-ℕ P p0 pS = refl

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → cases-leq-succ-ℕ {succ-ℕ n} {n} (refl-leq-ℕ n) ＝ inr refl
cases-leq-succ-reflexive-leq-ℕ {zero-ℕ} = refl
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} =
  ap (map-coprod id (ap succ-ℕ)) cases-leq-succ-reflexive-leq-ℕ

cases-eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
      ( λ k z m₁ z₁ →
        cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
      n m p) ＝
    ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  ( succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n) m p) ＝
  ( strong-ind-ℕ P p0 pS m)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p₁))
          n)
        ( succ-ℕ n))
       cases-leq-succ-reflexive-leq-ℕ))

eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
    ( λ k z m₁ z₁ →
      cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
    n m p) ＝
  ( strong-ind-ℕ P p0 pS m)
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ star = refl
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ (succ-ℕ m) ()
eq-comp-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-comp-succ-strong-ind-ℕ P p0 pS n
    ( eq-comp-succ-strong-ind-ℕ P p0 pS n) m p
    ( cases-leq-succ-ℕ p)

comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  strong-ind-ℕ P p0 pS (succ-ℕ n) ＝ pS n (λ m p → strong-ind-ℕ P p0 pS m)
comp-succ-strong-ind-ℕ P p0 pS n =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( refl-leq-ℕ n)) ∙
  ( ap ( pS n)
       ( eq-htpy
         ( λ m → eq-htpy
           ( λ p → eq-comp-succ-strong-ind-ℕ P p0 pS n m p))))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( h zero-ℕ ＝ p0) ×
      ( (n : ℕ) → h (succ-ℕ n) ＝ pS n (λ m p → h m)))
pr1 (total-strong-ind-ℕ P p0 pS) = strong-ind-ℕ P p0 pS
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-zero-strong-ind-ℕ P p0 pS
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-succ-strong-ind-ℕ P p0 pS
```
