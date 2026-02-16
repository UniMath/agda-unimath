# Dyadic sums on finite boolean sequences

```agda
module elementary-number-theory.dyadic-sums-bounded-boolean-predicates where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.geometric-sequences-rational-numbers
open import elementary-number-theory.inequalities-sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import set-theory.adjoining-indices-boolean-sequences

open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### Finite boolean sequences

```agda
bounded-sequence-bool : UU lzero
bounded-sequence-bool =
  Σ ℕ (λ k → Fin k → bool)
```

```agda
sequence-bool-bounded-sequence-bool :
  bounded-sequence-bool → ℕ → bool
sequence-bool-bounded-sequence-bool (zero-ℕ , χ) n =
  false
sequence-bool-bounded-sequence-bool (succ-ℕ k , χ) n =
  rec-coproduct
    ( λ n<k →
      χ (standard-classical-Fin (succ-ℕ k) (n , n<k)))
    ( λ _ → false)
    ( is-decidable-le-ℕ n (succ-ℕ k))
```

```agda
is-false-sequence-bool-bounded-sequence-bool-zero :
  (m : ℕ) →
  is-false (sequence-bool-bounded-sequence-bool (zero-ℕ , (λ ())) m)
is-false-sequence-bool-bounded-sequence-bool-zero m = refl
```

```agda
eq-sequence-bool-bounded-sequence-bool-nat-Fin :
  (S : bounded-sequence-bool) (i : Fin (pr1 S)) →
  sequence-bool-bounded-sequence-bool S (nat-Fin (pr1 S) i) ＝ pr2 S i
eq-sequence-bool-bounded-sequence-bool-nat-Fin (zero-ℕ , χ) ()
eq-sequence-bool-bounded-sequence-bool-nat-Fin (succ-ℕ k , χ) i =
  ind-coproduct
    ( λ d →
      rec-coproduct
        ( λ n<k →
          χ (standard-classical-Fin (succ-ℕ k) (nat-Fin (succ-ℕ k) i , n<k)))
        ( λ _ → false)
        d ＝
      χ i)
    ( λ n<k →
      ap χ
        ( is-injective-nat-Fin (succ-ℕ k)
          ( ap
            pr1
            ( is-retraction-classical-standard-Fin
              {succ-ℕ k}
              ( nat-Fin (succ-ℕ k) i , n<k)))))
    ( λ n≮k →
      ex-falso
        ( n≮k (strict-upper-bound-nat-Fin (succ-ℕ k) i)))
    ( is-decidable-le-ℕ (nat-Fin (succ-ℕ k) i) (succ-ℕ k))
```

### Negative powers of two

```agda
power-one-half-ℚ : ℕ → ℚ
power-one-half-ℚ n = power-ℚ n one-half-ℚ
```

### Dyadic summands

```agda
dyadic-summand-bool-ℚ : ℕ → bool → ℚ
dyadic-summand-bool-ℚ n =
  rec-bool (power-one-half-ℚ n) zero-ℚ
```

### The dyadic sum associated to a truncated boolean predicate

```agda
dyadic-sum-ℚ-bounded-sequence-bool :
  bounded-sequence-bool → ℚ
dyadic-sum-ℚ-bounded-sequence-bool (k , χ) =
  sum-fin-sequence-ℚ k
    ( λ i →
      dyadic-summand-bool-ℚ
        ( nat-Fin k i)
        ( χ i))
```

## Properties

### Negative powers of two are nonnegative

```agda
abstract
  leq-zero-power-one-half-ℚ :
    (n : ℕ) → leq-ℚ zero-ℚ (power-one-half-ℚ n)
  leq-zero-power-one-half-ℚ n =
    leq-le-ℚ (le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺))
```

```agda
  leq-dyadic-summand-bool-ℚ :
    (n : ℕ) (b : bool) →
    leq-ℚ (dyadic-summand-bool-ℚ n b) (power-one-half-ℚ n)
  leq-dyadic-summand-bool-ℚ n true =
    refl-leq-ℚ (power-one-half-ℚ n)
  leq-dyadic-summand-bool-ℚ n false =
    leq-zero-power-one-half-ℚ n

  leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ :
    (S : bounded-sequence-bool) →
    leq-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( sum-fin-sequence-ℚ
        ( pr1 S)
        ( λ i → power-one-half-ℚ (nat-Fin (pr1 S) i)))
  leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ (k , χ) =
    preserves-leq-sum-fin-sequence-ℚ
      ( k)
      ( λ i →
        dyadic-summand-bool-ℚ
          ( nat-Fin k i)
          ( χ i))
      ( λ i → power-one-half-ℚ (nat-Fin k i))
      ( λ i →
        leq-dyadic-summand-bool-ℚ
          ( nat-Fin k i)
          ( χ i))
```

```agda
  eq-full-dyadic-sum-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    sum-fin-sequence-ℚ k (λ i → power-one-half-ℚ (nat-Fin k i)) ＝
    sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k
  eq-full-dyadic-sum-sum-standard-geometric-one-half-ℚ k =
    ap
      ( sum-fin-sequence-ℚ k)
      ( eq-htpy
        ( λ i →
          inv
            ( ( compute-standard-geometric-sequence-ℚ
                ( one-ℚ)
                ( one-half-ℚ)
                ( nat-Fin k i)) ∙
              ( left-unit-law-mul-ℚ (power-ℚ (nat-Fin k i) one-half-ℚ)))))

  leq-two-full-dyadic-sum-ℚ-bounded-sequence-bool :
    (k : ℕ) →
    leq-ℚ
      ( sum-fin-sequence-ℚ k (λ i → power-one-half-ℚ (nat-Fin k i)))
      ( rational-ℕ 2)
  leq-two-full-dyadic-sum-ℚ-bounded-sequence-bool k =
    transitive-leq-ℚ _ _ _
      ( leq-rational-two-sum-standard-geometric-one-half-ℚ k)
      ( leq-eq-ℚ (eq-full-dyadic-sum-sum-standard-geometric-one-half-ℚ k))

  leq-two-dyadic-sum-ℚ-bounded-sequence-bool :
    (S : bounded-sequence-bool) →
    leq-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( rational-ℕ 2)
  leq-two-dyadic-sum-ℚ-bounded-sequence-bool (k , χ) =
    transitive-leq-ℚ _ _ _
      ( leq-two-full-dyadic-sum-ℚ-bounded-sequence-bool k)
      ( leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ
        ( k , χ))
```

## Adjoining indices to finite boolean sequences

```agda
adjoin-index-bounded-sequence-bool :
  bounded-sequence-bool → ℕ → bounded-sequence-bool
adjoin-index-bounded-sequence-bool (k , χ) n =
  ( k +ℕ succ-ℕ n ,
    λ i →
      force-true-at-sequence-bool
        (sequence-bool-bounded-sequence-bool (k , χ))
        n
        (nat-Fin (k +ℕ succ-ℕ n) i))
```

```agda
eq-nat-standard-classical-Fin :
  (k m : ℕ) (m<k : le-ℕ m k) →
  nat-Fin k (standard-classical-Fin k (m , m<k)) ＝ m
eq-nat-standard-classical-Fin k m m<k =
  ap pr1 (is-retraction-classical-standard-Fin {k} (m , m<k))

is-true-adjoin-index-bounded-sequence-bool :
  (S : bounded-sequence-bool) (n m : ℕ) →
  is-true
    ( sequence-bool-bounded-sequence-bool
      ( adjoin-index-bounded-sequence-bool S n)
      ( m)) →
  (m ＝ n) + is-true (sequence-bool-bounded-sequence-bool S m)
is-true-adjoin-index-bounded-sequence-bool S@(k , χ) n m =
  ind-coproduct
    ( λ d →
      is-true
        ( rec-coproduct
          ( λ m<k+n+1 →
            force-true-at-sequence-bool
              ( sequence-bool-bounded-sequence-bool S)
              ( n)
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                ( standard-classical-Fin
                  ( k +ℕ succ-ℕ n)
                  ( m , m<k+n+1))))
          ( λ _ → false)
          d) →
      (m ＝ n) + is-true (sequence-bool-bounded-sequence-bool S m))
    ( λ m<k+n+1 H →
      is-true-force-true-at-sequence-bool
        ( sequence-bool-bounded-sequence-bool S)
        ( n)
        ( m)
        ( tr
          is-true
          ( ap
            ( force-true-at-sequence-bool
              ( sequence-bool-bounded-sequence-bool S)
              ( n))
            ( eq-nat-standard-classical-Fin
              ( k +ℕ succ-ℕ n)
              ( m)
              ( m<k+n+1)))
          ( H)))
    ( λ _ ())
    ( is-decidable-le-ℕ m (k +ℕ succ-ℕ n))
```

We compare the dyadic sum on $χ$ and the dyadic sum on $n$ adjoined to $χ$,
$χ'$. We obtain

$$
  ∑_{i < k} χ(i)2⁻ⁱ ≤ ∑_{j < k + n + 1} χ'(j)2⁻ʲ,
$$

and, when $χ(n)$ is false,

$$
  ∑_{i < k} χ(i)2⁻ⁱ + 2⁻ⁿ ≤ ∑_{j < k + n + 1} χ'(j)2⁻ʲ.
$$

```agda
module _
  (n : ℕ) (S@(k , χ) : bounded-sequence-bool)
  where

  χℕ : ℕ → bool
  χℕ = sequence-bool-bounded-sequence-bool S

  summand-underlying-finseq-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-underlying-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ (nat-Fin k i) (χ i)

  summand-finseq-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  summand-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-at-sequence-bool χℕ n (nat-Fin (k +ℕ succ-ℕ n) i))

  summand-inl-finseq-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-inl-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin k i)
      ( force-true-at-sequence-bool χℕ n (nat-Fin k i))

  summand-inr-finseq-adjoin-index-bounded-sequence-bool :
    Fin (succ-ℕ n) → ℚ
  summand-inr-finseq-adjoin-index-bounded-sequence-bool =
    summand-finseq-adjoin-index-bounded-sequence-bool ∘
    inr-coproduct-Fin k (succ-ℕ n)

  abstract
    leq-summand-underlying-inl-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin k) →
      leq-ℚ
        ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool i)
        ( summand-inl-finseq-adjoin-index-bounded-sequence-bool i)
    leq-summand-underlying-inl-finseq-adjoin-index-bounded-sequence-bool
      i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool i)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin k i)
              ( force-true-at-sequence-bool χℕ n (nat-Fin k i))))
        ( λ p →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin k i))
                  ( eq-force-true-at-eq-sequence-bool χℕ n (nat-Fin k i) p))))
            ( ind-bool
              ( λ b →
                leq-ℚ
                  ( dyadic-summand-bool-ℚ (nat-Fin k i) b)
                  ( power-one-half-ℚ (nat-Fin k i)))
              ( refl-leq-ℚ (power-one-half-ℚ (nat-Fin k i)))
              ( leq-zero-power-one-half-ℚ (nat-Fin k i))
              ( χ i)))
        ( λ q →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin k i))
                  ( eq-force-true-at-neq-sequence-bool χℕ n (nat-Fin k i) q))))
            ( leq-eq-ℚ
              ( ap
                ( dyadic-summand-bool-ℚ (nat-Fin k i))
                ( inv (eq-sequence-bool-bounded-sequence-bool-nat-Fin S i)))))
        ( has-decidable-equality-ℕ (nat-Fin k i) n)

    leq-zero-summand-inr-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( summand-inr-finseq-adjoin-index-bounded-sequence-bool i)
    leq-zero-summand-inr-finseq-adjoin-index-bounded-sequence-bool
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i))
              ( b)))
        ( leq-zero-power-one-half-ℚ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-at-sequence-bool χℕ n
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    leq-zero-sum-summand-inr-finseq-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( zero-ℚ)
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( summand-inr-finseq-adjoin-index-bounded-sequence-bool))
    leq-zero-sum-summand-inr-finseq-adjoin-index-bounded-sequence-bool =
      leq-zero-sum-fin-sequence-ℚ
        ( succ-ℕ n)
        ( summand-inr-finseq-adjoin-index-bounded-sequence-bool)
        ( leq-zero-summand-inr-finseq-adjoin-index-bounded-sequence-bool)

  leq-sum-underlying-finseq-sum-inl-extended-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( sum-fin-sequence-ℚ k
        ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool))
      ( sum-fin-sequence-ℚ k
        ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n)))
  leq-sum-underlying-finseq-sum-inl-extended-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-eq-ℚ
        ( ap
          ( sum-fin-sequence-ℚ k)
          ( eq-htpy
            ( λ i →
              ap
                ( λ m →
                  dyadic-summand-bool-ℚ m
                    ( force-true-at-sequence-bool χℕ n m))
                ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))))))
      ( preserves-leq-sum-fin-sequence-ℚ k
        ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool)
        ( summand-inl-finseq-adjoin-index-bounded-sequence-bool)
        ( leq-summand-underlying-inl-finseq-adjoin-index-bounded-sequence-bool))

  leq-sum-inl-extended-finseq-sum-summand-finseq-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( sum-fin-sequence-ℚ k
        ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n)))
      ( sum-fin-sequence-ℚ
        ( k +ℕ succ-ℕ n)
        ( summand-finseq-adjoin-index-bounded-sequence-bool))
  leq-sum-inl-extended-finseq-sum-summand-finseq-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-eq-ℚ
        ( inv
          ( split-sum-fin-sequence-ℚ k
            ( succ-ℕ n)
            ( summand-finseq-adjoin-index-bounded-sequence-bool))))
      ( transitive-leq-ℚ _ _ _
        ( preserves-leq-right-add-ℚ
          ( sum-fin-sequence-ℚ k
            ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
              inl-coproduct-Fin k (succ-ℕ n)))
          ( zero-ℚ)
          ( sum-fin-sequence-ℚ
            ( succ-ℕ n)
            ( summand-inr-finseq-adjoin-index-bounded-sequence-bool))
          ( leq-zero-sum-summand-inr-finseq-adjoin-index-bounded-sequence-bool))
        ( leq-eq-ℚ
          ( inv
            ( right-unit-law-add-ℚ
              ( sum-fin-sequence-ℚ k
                ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
                  inl-coproduct-Fin k (succ-ℕ n)))))))

  leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( dyadic-sum-ℚ-bounded-sequence-bool
        ( adjoin-index-bounded-sequence-bool S n))
  leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-sum-inl-extended-finseq-sum-summand-finseq-adjoin-index-bounded-sequence-bool)
      ( leq-sum-underlying-finseq-sum-inl-extended-adjoin-index-bounded-sequence-bool)

  underlying-extended-finseq-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  underlying-extended-finseq-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( χℕ (nat-Fin (k +ℕ succ-ℕ n) i))

  inl-underlying-extended-finseq-bounded-sequence-bool :
    Fin k → ℚ
  inl-underlying-extended-finseq-bounded-sequence-bool =
    underlying-extended-finseq-bounded-sequence-bool ∘
    inl-coproduct-Fin k (succ-ℕ n)

  inr-underlying-extended-finseq-bounded-sequence-bool :
    Fin (succ-ℕ n) → ℚ
  inr-underlying-extended-finseq-bounded-sequence-bool =
    underlying-extended-finseq-bounded-sequence-bool ∘
    inr-coproduct-Fin k (succ-ℕ n)

  delta-finseq-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  delta-finseq-adjoin-index-bounded-sequence-bool i =
    rec-coproduct
      ( λ _ → power-one-half-ℚ n)
      ( λ _ → zero-ℚ)
      ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool :
      (i : Fin k) →
      summand-underlying-finseq-adjoin-index-bounded-sequence-bool i ＝
      inl-underlying-extended-finseq-bounded-sequence-bool i
    eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool
      i =
      ( ap
        ( dyadic-summand-bool-ℚ (nat-Fin k i))
        ( inv (eq-sequence-bool-bounded-sequence-bool-nat-Fin S i))) ∙
      ( ap
        ( λ m → dyadic-summand-bool-ℚ m (χℕ m))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i)))

    leq-zero-inr-underlying-extended-finseq-bounded-sequence-bool :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( inr-underlying-extended-finseq-bounded-sequence-bool i)
    leq-zero-inr-underlying-extended-finseq-bounded-sequence-bool
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i))
              ( b)))
        ( leq-zero-power-one-half-ℚ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( χℕ (nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    leq-sum-underlying-finseq-sum-underlying-extended-finseq-bounded-sequence-bool :
      leq-ℚ
        ( sum-fin-sequence-ℚ k
          ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool))
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( underlying-extended-finseq-bounded-sequence-bool))
    leq-sum-underlying-finseq-sum-underlying-extended-finseq-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( inv
              ( split-sum-fin-sequence-ℚ
                ( k)
                ( succ-ℕ n)
                ( underlying-extended-finseq-bounded-sequence-bool))))
          ( transitive-leq-ℚ _ _ _
            ( preserves-leq-right-add-ℚ
              ( sum-fin-sequence-ℚ k
                ( inl-underlying-extended-finseq-bounded-sequence-bool))
              ( zero-ℚ)
              ( sum-fin-sequence-ℚ
                ( succ-ℕ n)
                ( inr-underlying-extended-finseq-bounded-sequence-bool))
              ( leq-zero-sum-fin-sequence-ℚ
                ( succ-ℕ n)
                ( inr-underlying-extended-finseq-bounded-sequence-bool)
                ( leq-zero-inr-underlying-extended-finseq-bounded-sequence-bool)))
            ( leq-eq-ℚ
              ( inv
                ( right-unit-law-add-ℚ
                  ( sum-fin-sequence-ℚ k
                    ( inl-underlying-extended-finseq-bounded-sequence-bool)))))))
        ( leq-eq-ℚ
          ( ap
            ( sum-fin-sequence-ℚ k)
            ( eq-htpy
              ( eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool))))

    eq-delta-finseq-selected-adjoin-index-bounded-sequence-bool :
      delta-finseq-adjoin-index-bounded-sequence-bool (mod-succ-ℕ (k +ℕ n) n) ＝
      power-one-half-ℚ n
    eq-delta-finseq-selected-adjoin-index-bounded-sequence-bool =
      ind-coproduct
        ( λ d →
          rec-coproduct (λ _ → power-one-half-ℚ n) (λ _ → zero-ℚ) d ＝
          power-one-half-ℚ n)
        ( λ _ → refl)
        ( λ q → ex-falso (q (eq-nat-fin-mod-add-succ-ℕ k n)))
        ( has-decidable-equality-ℕ
          ( nat-Fin (k +ℕ succ-ℕ n) (mod-succ-ℕ (k +ℕ n) n))
          ( n))

    leq-zero-delta-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( delta-finseq-adjoin-index-bounded-sequence-bool i)
    leq-zero-delta-finseq-adjoin-index-bounded-sequence-bool i
      =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( zero-ℚ)
            ( rec-coproduct (λ _ → power-one-half-ℚ n) (λ _ → zero-ℚ) d))
        ( λ _ → leq-zero-power-one-half-ℚ n)
        ( λ _ → refl-leq-ℚ zero-ℚ)
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    leq-power-one-half-sum-delta-finseq-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( power-one-half-ℚ n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-finseq-adjoin-index-bounded-sequence-bool))
    leq-power-one-half-sum-delta-finseq-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-zero-delta-finseq-adjoin-index-bounded-sequence-bool)
          ( mod-succ-ℕ (k +ℕ n) n))
        ( leq-eq-ℚ
          ( inv eq-delta-finseq-selected-adjoin-index-bounded-sequence-bool))

    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool :
      is-false (χℕ n) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( underlying-extended-finseq-bounded-sequence-bool i +ℚ
          delta-finseq-adjoin-index-bounded-sequence-bool i)
        ( summand-finseq-adjoin-index-bounded-sequence-bool i)
    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool
      χn=false i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( underlying-extended-finseq-bounded-sequence-bool i +ℚ
              rec-coproduct (λ _ → power-one-half-ℚ n) (λ _ → zero-ℚ) d)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin (k +ℕ succ-ℕ n) i)
              ( force-true-at-sequence-bool χℕ n (nat-Fin (k +ℕ succ-ℕ n) i))))
        ( λ p →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ( ap
                    ( dyadic-summand-bool-ℚ
                      ( nat-Fin (k +ℕ succ-ℕ n) i))
                    ( eq-force-true-at-eq-sequence-bool χℕ n
                      ( nat-Fin (k +ℕ succ-ℕ n) i)
                      ( p))) ∙
                  ( ap power-one-half-ℚ p))))
            ( transitive-leq-ℚ _ _ _
              ( ind-bool
                ( λ b →
                  is-false b →
                  leq-ℚ
                    ( dyadic-summand-bool-ℚ n b +ℚ power-one-half-ℚ n)
                    ( power-one-half-ℚ n))
                ( λ ())
                ( λ _ →
                  leq-eq-ℚ
                    ( left-unit-law-add-ℚ (power-one-half-ℚ n)))
                ( χℕ n)
                ( χn=false))
              ( leq-eq-ℚ
                ( ap
                  ( λ m → dyadic-summand-bool-ℚ m (χℕ m) +ℚ power-one-half-ℚ n)
                  ( p)))))
        ( λ q →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin (k +ℕ succ-ℕ n) i))
                  ( eq-force-true-at-neq-sequence-bool χℕ n
                    ( nat-Fin (k +ℕ succ-ℕ n) i)
                    ( q)))))
            ( transitive-leq-ℚ _ _ _
              ( leq-eq-ℚ
                ( right-unit-law-add-ℚ
                  ( underlying-extended-finseq-bounded-sequence-bool i)))
              ( refl-leq-ℚ _)))
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    leq-dyadic-sum+bool-power-one-half-sum-adjoin-index-bounded-sequence-bool :
      is-false (χℕ n) →
      leq-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-one-half-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-dyadic-sum+bool-power-one-half-sum-adjoin-index-bounded-sequence-bool
      χn=false =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( λ i →
            underlying-extended-finseq-bounded-sequence-bool i +ℚ
            delta-finseq-adjoin-index-bounded-sequence-bool i)
          ( summand-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool
            ( χn=false)))
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( interchange-add-sum-fin-sequence-ℚ
              ( k +ℕ succ-ℕ n)
              ( underlying-extended-finseq-bounded-sequence-bool)
              ( delta-finseq-adjoin-index-bounded-sequence-bool)))
          ( preserves-leq-add-ℚ
            ( leq-sum-underlying-finseq-sum-underlying-extended-finseq-bounded-sequence-bool)
            ( leq-power-one-half-sum-delta-finseq-adjoin-index-bounded-sequence-bool)))

    leq-delta-summand-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( delta-finseq-adjoin-index-bounded-sequence-bool i)
        ( summand-finseq-adjoin-index-bounded-sequence-bool i)
    leq-delta-summand-finseq-adjoin-index-bounded-sequence-bool i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( rec-coproduct (λ _ → power-one-half-ℚ n) (λ _ → zero-ℚ) d)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin (k +ℕ succ-ℕ n) i)
              ( force-true-at-sequence-bool χℕ n (nat-Fin (k +ℕ succ-ℕ n) i))))
        ( λ p →
          leq-eq-ℚ
            ( inv
              ( ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin (k +ℕ succ-ℕ n) i))
                  ( eq-force-true-at-eq-sequence-bool χℕ n
                    ( nat-Fin (k +ℕ succ-ℕ n) i)
                    ( p))) ∙
                ( ap power-one-half-ℚ p))))
        ( λ _ →
          ind-bool
            ( λ b →
              leq-ℚ
                ( zero-ℚ)
                ( dyadic-summand-bool-ℚ (nat-Fin (k +ℕ succ-ℕ n) i) b))
            ( leq-zero-power-one-half-ℚ (nat-Fin (k +ℕ succ-ℕ n) i))
            ( refl-leq-ℚ zero-ℚ)
            ( force-true-at-sequence-bool χℕ n (nat-Fin (k +ℕ succ-ℕ n) i)))
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    leq-power-one-half-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( power-one-half-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-power-one-half-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-finseq-adjoin-index-bounded-sequence-bool)
          ( summand-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-delta-summand-finseq-adjoin-index-bounded-sequence-bool))
        ( leq-power-one-half-sum-delta-finseq-adjoin-index-bounded-sequence-bool)
```

### Negative powers of two are positive

```agda
abstract
  le-zero-power-one-half-ℚ :
    (n : ℕ) → le-ℚ zero-ℚ (power-one-half-ℚ n)
  le-zero-power-one-half-ℚ n =
    le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺)
```
