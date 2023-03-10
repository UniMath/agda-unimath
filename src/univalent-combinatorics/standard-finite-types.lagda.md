# The standard finite types

```agda
module univalent-combinatorics.standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.noncontractible-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The standard finite types are defined inductively by `Fin 0 := empty` and `Fin (n+1) := (Fin n) + 1`. **Note** that the outermost coproduct (i.e. the `inr` injection) is the _top_ element, when `Fin n` is considered as an initial segment of `n`.

## Definition

### The standard finite types in universe level zero.

```agda
Fin-Set : ℕ → Set lzero
Fin-Set zero-ℕ = empty-Set
Fin-Set (succ-ℕ n) = coprod-Set (Fin-Set n) unit-Set

Fin : ℕ → UU lzero
Fin n = type-Set (Fin-Set n)

is-set-Fin : (n : ℕ) → is-set (Fin n)
is-set-Fin n = is-set-type-Set (Fin-Set n)

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

emb-inl-Fin : (k : ℕ) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-inl-Fin k) = inl-Fin k
pr2 (emb-inl-Fin k) = is-emb-inl (Fin k) unit

neg-one-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-one-Fin k = inr star

is-neg-one-Fin : (k : ℕ) → Fin k → UU lzero
is-neg-one-Fin (succ-ℕ k) x = x ＝ neg-one-Fin k

neg-two-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-two-Fin zero-ℕ = inr star
neg-two-Fin (succ-ℕ k) = inl (inr star)

is-inl-Fin : (k : ℕ) → Fin (succ-ℕ k) → UU lzero
is-inl-Fin k x = Σ (Fin k) (λ y → inl y ＝ x)

is-neg-one-is-not-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  ¬ (is-inl-Fin k x) → is-neg-one-Fin (succ-ℕ k) x
is-neg-one-is-not-inl-Fin k (inl x) H = ex-falso (H (pair x refl))
is-neg-one-is-not-inl-Fin k (inr star) H = refl

inr-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
inr-Fin (succ-ℕ k) (inl x) = inl (inr-Fin k x)
inr-Fin (succ-ℕ k) (inr star) = inr star
```

### The standard finite types in an arbitrary universe

```agda
raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

compute-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
compute-raise-Fin l k = compute-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

raise-Fin-Set : (l : Level) (k : ℕ) → Set l
raise-Fin-Set l k = raise-Set l (Fin-Set k)
```

## Properties

### Being on the left is decidable

```agda
is-decidable-is-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin k x)
is-decidable-is-inl-Fin k (inl x) = inl (pair x refl)
is-decidable-is-inl-Fin k (inr star) = inr α
  where
  α : is-inl-Fin k (inr star) → empty
  α (pair y ())
```

### Fin 1 is contractible

```agda
map-equiv-Fin-one-ℕ : Fin 1 → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin 1
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin 1 ≃ unit
pr1 equiv-Fin-one-ℕ = map-equiv-Fin-one-ℕ
pr2 equiv-Fin-one-ℕ = is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin 1)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  neq-inl-inr (eq-is-contr' C (neg-two-Fin (succ-ℕ k)) (neg-one-Fin (succ-ℕ k)))
```

### The inclusion of Fin k into ℕ

```agda
nat-Fin : (k : ℕ) → Fin k → ℕ
nat-Fin (succ-ℕ k) (inl x) = nat-Fin k x
nat-Fin (succ-ℕ k) (inr x) = k

strict-upper-bound-nat-Fin : (k : ℕ) (x : Fin k) → le-ℕ (nat-Fin k x) k
strict-upper-bound-nat-Fin (succ-ℕ k) (inl x) =
  transitive-le-ℕ
    ( nat-Fin k x)
    ( k)
    ( succ-ℕ k)
    ( strict-upper-bound-nat-Fin k x)
    ( succ-le-ℕ k)
strict-upper-bound-nat-Fin (succ-ℕ k) (inr star) =
  succ-le-ℕ k

upper-bound-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin (succ-ℕ k) x) k
upper-bound-nat-Fin zero-ℕ (inr star) = star
upper-bound-nat-Fin (succ-ℕ k) (inl x) =
  preserves-leq-succ-ℕ (nat-Fin (succ-ℕ k) x) k (upper-bound-nat-Fin k x)
upper-bound-nat-Fin (succ-ℕ k) (inr star) = refl-leq-ℕ (succ-ℕ k)

is-injective-nat-Fin : (k : ℕ) → is-injective (nat-Fin k)
is-injective-nat-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin k p)
is-injective-nat-Fin (succ-ℕ k) {inl x} {inr star} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin k x) p)
is-injective-nat-Fin (succ-ℕ k) {inr star} {inl y} p =
  ex-falso (neq-le-ℕ (strict-upper-bound-nat-Fin k y) (inv p))
is-injective-nat-Fin (succ-ℕ k) {inr star} {inr star} p =
  refl

is-emb-nat-Fin : (k : ℕ) → is-emb (nat-Fin k)
is-emb-nat-Fin k = is-emb-is-injective is-set-ℕ (is-injective-nat-Fin k)

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = nat-Fin k
pr2 (emb-nat-Fin k) = is-emb-nat-Fin k
```

### The zero elements in the standard finite types

```agda
zero-Fin : (k : ℕ) → Fin (succ-ℕ k)
zero-Fin zero-ℕ = inr star
zero-Fin (succ-ℕ k) = inl (zero-Fin k)

is-zero-Fin : (k : ℕ) → Fin k → UU lzero
is-zero-Fin (succ-ℕ k) x = x ＝ zero-Fin k

is-zero-Fin' : (k : ℕ) → Fin k → UU lzero
is-zero-Fin' (succ-ℕ k) x = zero-Fin k ＝ x

is-nonzero-Fin : (k : ℕ) → Fin k → UU lzero
is-nonzero-Fin (succ-ℕ k) x = ¬ (is-zero-Fin (succ-ℕ k) x)
```

### The successor function on the standard finite types

```agda
skip-zero-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-zero-Fin (succ-ℕ k) (inl x) = inl (skip-zero-Fin k x)
skip-zero-Fin (succ-ℕ k) (inr star) = inr star

succ-Fin : (k : ℕ) → Fin k → Fin k
succ-Fin (succ-ℕ k) (inl x) = skip-zero-Fin k x
succ-Fin (succ-ℕ k) (inr star) = (zero-Fin k)

Fin-Endo : ℕ → Endo lzero
pr1 (Fin-Endo k) = Fin k
pr2 (Fin-Endo k) = succ-Fin k
```

```agda
is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (succ-ℕ k) (zero-Fin k))
is-zero-nat-zero-Fin {zero-ℕ} = refl
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

nat-skip-zero-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (skip-zero-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-skip-zero-Fin (succ-ℕ k) (inl x) = nat-skip-zero-Fin k x
nat-skip-zero-Fin (succ-ℕ k) (inr star) = refl

nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x)) ＝ succ-ℕ (nat-Fin k x)
nat-succ-Fin k x = nat-skip-zero-Fin k x

nat-inr-Fin :
  (k : ℕ) (x : Fin k) → nat-Fin (succ-ℕ k) (inr-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-inr-Fin (succ-ℕ k) (inl x) = nat-inr-Fin k x
nat-inr-Fin (succ-ℕ k) (inr star) = refl
```

```agda
one-Fin : (k : ℕ) → Fin (succ-ℕ k)
one-Fin k = succ-Fin (succ-ℕ k) (zero-Fin k)

is-one-Fin : (k : ℕ) → Fin k → UU lzero
is-one-Fin (succ-ℕ k) x = x ＝ one-Fin k

is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → (is-zero-Fin 2 x) + (is-one-Fin 2 x)
is-zero-or-one-Fin-two-ℕ (inl (inr star)) = inl refl
is-zero-or-one-Fin-two-ℕ (inr star) = inr refl

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k)))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k
```

```agda
is-injective-inl-Fin : (k : ℕ) → is-injective (inl-Fin k)
is-injective-inl-Fin k refl = refl

-- Exercise 7.5 (c)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} → is-nonzero-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin (succ-ℕ k) p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} ()

-- Exercise 7.5 (d)

is-injective-skip-zero-Fin : (k : ℕ) → is-injective (skip-zero-Fin k)
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k (is-injective-inl-Fin (succ-ℕ k) p))
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inr star} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inl y} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inr star} p = refl

is-injective-succ-Fin : (k : ℕ) → is-injective (succ-Fin k)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k {x} {y} p)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inr star} p = refl
```

```agda
-- We define a function skip-neg-two-Fin in order to define pred-Fin.

skip-neg-two-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin (succ-ℕ k) (inl x) = inl (inl x)
skip-neg-two-Fin (succ-ℕ k) (inr x) = neg-one-Fin (succ-ℕ k)

-- We define the predecessor function on Fin k.

pred-Fin : (k : ℕ) → Fin k → Fin k
pred-Fin (succ-ℕ k) (inl x) = skip-neg-two-Fin k (pred-Fin k x)
pred-Fin (succ-ℕ k) (inr x) = neg-two-Fin k

-- We now turn to the exercise.

pred-zero-Fin :
  (k : ℕ) → is-neg-one-Fin (succ-ℕ k) (pred-Fin (succ-ℕ k) (zero-Fin k))
pred-zero-Fin (zero-ℕ) = refl
pred-zero-Fin (succ-ℕ k) = ap (skip-neg-two-Fin (succ-ℕ k)) (pred-zero-Fin k)

succ-skip-neg-two-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ (succ-ℕ k)) (skip-neg-two-Fin (succ-ℕ k) x) ＝
  inl (succ-Fin (succ-ℕ k) x)
succ-skip-neg-two-Fin zero-ℕ (inr star) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inl x) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inr star) = refl

issec-pred-Fin :
  (k : ℕ) (x : Fin k) → succ-Fin k (pred-Fin k x) ＝ x
issec-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
issec-pred-Fin (succ-ℕ (succ-ℕ k)) (inl x) =
  ( succ-skip-neg-two-Fin k (pred-Fin (succ-ℕ k) x)) ∙
  ( ap inl (issec-pred-Fin (succ-ℕ k) x))
issec-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = refl

isretr-pred-Fin :
  (k : ℕ) (x : Fin k) → pred-Fin k (succ-Fin k x) ＝ x
isretr-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
isretr-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inl x)) =
  ap (skip-neg-two-Fin (succ-ℕ k)) (isretr-pred-Fin (succ-ℕ k) (inl x))
isretr-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inr star)) = refl
isretr-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = pred-zero-Fin (succ-ℕ k)

is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
pr1 (pr1 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr1 (is-equiv-succ-Fin k)) = issec-pred-Fin k
pr1 (pr2 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr2 (is-equiv-succ-Fin k)) = isretr-pred-Fin k

equiv-succ-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-succ-Fin k) = succ-Fin k
pr2 (equiv-succ-Fin k) = is-equiv-succ-Fin k

is-equiv-pred-Fin : (k : ℕ) → is-equiv (pred-Fin k)
pr1 (pr1 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr1 (is-equiv-pred-Fin k)) = isretr-pred-Fin k
pr1 (pr2 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr2 (is-equiv-pred-Fin k)) = issec-pred-Fin k

equiv-pred-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-pred-Fin k) = pred-Fin k
pr2 (equiv-pred-Fin k) = is-equiv-pred-Fin k
```

```agda
leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (succ-ℕ k) (skip-zero-Fin k x))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inl x)))
    ( nat-skip-zero-Fin k x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inr star)))
    ( is-zero-nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin (succ-ℕ k) (inr star))))
```

### Fin is injective

```agda
abstract
  is-injective-Fin : {k l : ℕ} → (Fin k ≃ Fin l) → k ＝ l
  is-injective-Fin {zero-ℕ} {zero-ℕ} e = refl
  is-injective-Fin {zero-ℕ} {succ-ℕ l} e =
    ex-falso (map-inv-equiv e (zero-Fin l))
  is-injective-Fin {succ-ℕ k} {zero-ℕ} e =
    ex-falso (map-equiv e (zero-Fin k))
  is-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
    ap succ-ℕ (is-injective-Fin (equiv-equiv-Maybe e))
```
