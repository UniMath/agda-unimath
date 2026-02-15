# Levy's uncountability argument for MacNeille real numbers, predicatively

```agda
module real-numbers.predicative-levy-uncountability-argument-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.geometric-sequences-rational-numbers
open import elementary-number-theory.inequalities-sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.powers-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-macneille-real-numbers
open import real-numbers.greatest-postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.increasing-endomaps-macneille-real-numbers
open import real-numbers.inequalities-addition-macneille-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.least-upper-bounds-families-macneille-real-numbers
open import real-numbers.least-upper-bounds-postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.least-upper-bounds-rational-translation-addition-macneille-real-numbers
open import real-numbers.located-macneille-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.not-in-image-greatest-postfixpoints-macneille-real-numbers
open import real-numbers.postfixpoints-endomaps-macneille-real-numbers
open import real-numbers.raising-universe-levels-located-macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.raising-universe-levels-rational-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.rational-translation-macneille-real-numbers
open import real-numbers.similarity-macneille-real-numbers
open import real-numbers.strict-inequality-macneille-real-numbers
open import real-numbers.upper-bounds-families-macneille-real-numbers

open import set-theory.adjoining-indices-boolean-sequences

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We formalize a predicative reconstruction of Blechschmidt–Hutzler's constructive
Knaster–Tarski proof of the uncountability of the
[MacNeille reals](real-numbers.macneille-real-numbers.md) {{#cite BH19}},
building on Levy's "unusual proof that the reals are uncountable"
{{#cite levy09}}.

**Theorem.** For every sequence of MacNeille reals $f$ we can construct some
$x₀ : ℝₘ$ such that for all $n : ℕ$, $f(n) ≠ x₀$.

In other words, the MacNeille reals are
[sequence-avoiding](set-theory.sequence-avoiding-sets.md) and hence uncountable,
which we register in the separate file
[`real-numbers.uncountability-macneille-real-numbers`](real-numbers.uncountability-macneille-real-numbers.md).

**Proof (outline).** Let $f$ be a sequence of MacNeille reals. For each
$x : ℝₘ$, we will say a subset $S$ of $ℕ$ is _admissible at_ $x$ if $i ∈ S$
implies that $x ≰ f(i)$. Thus elements of $S$ are required to lie to the right
of $x$ under $f$.

We assign to each subset $S$ the dyadic sum $∑_{i ∈ S}2⁻ⁱ$. This defines a
family of elements in $ℝₘ$ which is inhabited (take $S$ the empty subset) and
bounded above by $2$, since

$$
∑_{i ∈ S}2⁻ⁱ ≤ ∑_i 2⁻ⁱ = 2.
$$

Hence by
[order completeness of the MacNeille reals](real-numbers.least-upper-bounds-families-macneille-real-numbers.md)
it has a least upper bound; this defines an endomap $g : ℝₘ → ℝₘ$,

$$
g(x) ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ finite and admissible at }x\}.
$$

Note that finite subsets can be encoded as bounded boolean predicates
$χ : ℕ → bool$, so this construction is predicative.

Next, fix an index $n$ and adjoin it to $S$. This extension preserves finiteness
and yields the inequality $∑_{i ∈ S}2⁻ⁱ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ$. If $n ∉ S$,
then we may refine this inequality to:

$$
∑_{i ∈ S}2⁻ⁱ + 2⁻ⁿ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ.
$$

Now restrict to _self-admissible_ finite subsets $S$, in the sense that $S$ is
admissible at $∑_{i ∈ S}2⁻ⁱ$. Their associated dyadic sums form an inhabited
bounded family; let

$$
x₀ ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ is self-admissible finite subset}\}.
$$

Assume for the sake of reaching a contradiction that $f(n) = x₀$. Then $n ∉ S$
for any self-admissible finite subset $S$. Applying the extension inequality and
and using the fact that $x₀$ is a least upper bound yields

$$
x₀ + 2⁻ⁿ ≤ x₀.
$$

This contradicts the positivity of $2⁻ⁿ$. Therefore $f(n) ≠ x₀$ for all $n$. ∎

## The dyadic sum of a bounded boolean predicate

Fix $f : ℕ → ℝₘ$ and $x : ℝₘ$. The type `bounded-sequence-bool` encodes bounded
boolean predicates `χ : ℕ → bool`

Hence admissible selectors represent finite sets of indices that are extended to
lie to the right of $x$ under $f$.

```agda
bounded-sequence-bool : UU lzero
bounded-sequence-bool =
  Σ ℕ (λ k → Σ (ℕ → bool) (λ χ → (m : ℕ) → leq-ℕ k m → is-false (χ m)))
```

Each included index $n$ contributes the dyadic weight $2⁻ⁿ = (½)ⁿ$. The map
`selected-weight-...` realizes multiplication by the bounded boolean predicate:
if $χ(n) then $2⁻ⁿ$ for `true` and $0$ for `false`. Summation is taken over
`Fin k`, then embedded into MacNeille reals.

In symbols, this is $∑_{i < k} χ(i)2⁻ⁱ$, implemented by
`dyadic-sum-bounded-sequence-bool`.

```agda
weight-levy-sequence-macneille-ℝ : ℕ → ℚ
weight-levy-sequence-macneille-ℝ n =
  power-ℚ n one-half-ℚ

summand-levy-sequence-macneille-ℝ : ℕ → bool → ℚ
summand-levy-sequence-macneille-ℝ n =
  rec-bool (weight-levy-sequence-macneille-ℝ n) zero-ℚ

dyadic-sum-bounded-sequence-bool :
  bounded-sequence-bool → ℚ
dyadic-sum-bounded-sequence-bool (k , χ , _) =
  sum-fin-sequence-ℚ k
    ( λ i → summand-levy-sequence-macneille-ℝ (nat-Fin k i) (χ (nat-Fin k i)))

abstract
  leq-zero-weight-levy-sequence-macneille-ℝ :
    (n : ℕ) → leq-ℚ zero-ℚ (weight-levy-sequence-macneille-ℝ n)
  leq-zero-weight-levy-sequence-macneille-ℝ n =
    leq-le-ℚ (le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺))

  leq-summand-levy-sequence-macneille-ℝ :
    (n : ℕ) (b : bool) →
    leq-ℚ
      ( summand-levy-sequence-macneille-ℝ n b)
      ( weight-levy-sequence-macneille-ℝ n)
  leq-summand-levy-sequence-macneille-ℝ n true =
    refl-leq-ℚ (weight-levy-sequence-macneille-ℝ n)
  leq-summand-levy-sequence-macneille-ℝ n false =
    leq-zero-weight-levy-sequence-macneille-ℝ n

  leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ :
    (S : bounded-sequence-bool) →
    leq-ℚ
      ( dyadic-sum-bounded-sequence-bool S)
      ( sum-fin-sequence-ℚ
        ( pr1 S)
        ( λ i → weight-levy-sequence-macneille-ℝ (nat-Fin (pr1 S) i)))
  leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ (k , χ , _) =
    preserves-leq-sum-fin-sequence-ℚ
      ( k)
      ( λ i →
        summand-levy-sequence-macneille-ℝ
          ( nat-Fin k i)
          ( χ (nat-Fin k i)))
      ( λ i →
        weight-levy-sequence-macneille-ℝ (nat-Fin k i))
      ( λ i →
        leq-summand-levy-sequence-macneille-ℝ
          ( nat-Fin k i)
          ( χ (nat-Fin k i)))

  eq-sum-all-weights-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    sum-fin-sequence-ℚ
      ( k)
      ( λ i → weight-levy-sequence-macneille-ℝ (nat-Fin k i)) ＝
    sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k
  eq-sum-all-weights-sum-standard-geometric-one-half-ℚ k =
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

  leq-two-sum-all-weights-bounded-sequence-bool :
    (k : ℕ) →
    leq-ℚ
      ( sum-fin-sequence-ℚ
        ( k)
        ( λ i → weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
      ( rational-ℕ 2)
  leq-two-sum-all-weights-bounded-sequence-bool k =
    transitive-leq-ℚ _ _ _
      ( leq-rational-two-sum-standard-geometric-one-half-ℚ k)
      ( leq-eq-ℚ (eq-sum-all-weights-sum-standard-geometric-one-half-ℚ k))

  leq-two-dyadic-sum-bounded-sequence-bool :
    (S : bounded-sequence-bool) →
    leq-ℚ
      ( dyadic-sum-bounded-sequence-bool S)
      ( rational-ℕ 2)
  leq-two-dyadic-sum-bounded-sequence-bool (k , χ , adm-χ) =
    transitive-leq-ℚ _ _ _
      ( leq-two-sum-all-weights-bounded-sequence-bool k)
      ( leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ
        ( k , χ , adm-χ))
```

The inequalities above establish

$$
∑_{i < k}χ(i)2⁻ⁱ ≤ ∑_{i < k}2⁻ⁱ ≤ 2.
$$

So the family is inhabited and bounded, and we can define Levy’s endomap

$$
g(x) ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ finite and admissible at }x\}.
$$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l)
  where

  is-levy-admissible-bounded-sequence-bool :
    bounded-sequence-bool → UU l
  is-levy-admissible-bounded-sequence-bool (k , χ , _) =
    (m : ℕ) → is-true (χ m) → ¬ leq-macneille-ℝ x (f m)

  indexing-type-levy-family-sequence-macneille-ℝ : UU l
  indexing-type-levy-family-sequence-macneille-ℝ =
    Σ ( bounded-sequence-bool)
      ( is-levy-admissible-bounded-sequence-bool)

  family-of-elements-levy-sequence-macneille-ℝ :
    indexing-type-levy-family-sequence-macneille-ℝ →
    macneille-ℝ l
  family-of-elements-levy-sequence-macneille-ℝ (S , _) =
    raise-macneille-real-ℚ l (dyadic-sum-bounded-sequence-bool S)

  point-indexing-type-levy-family-sequence-macneille-ℝ :
    indexing-type-levy-family-sequence-macneille-ℝ
  point-indexing-type-levy-family-sequence-macneille-ℝ =
    ((zero-ℕ , (λ _ → false) , (λ _ _ → refl)) , (λ _ ()))

  is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ :
    is-inhabited indexing-type-levy-family-sequence-macneille-ℝ
  is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ =
    unit-trunc-Prop point-indexing-type-levy-family-sequence-macneille-ℝ

  upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
    macneille-ℝ l
  upper-bound-family-of-elements-levy-sequence-macneille-ℝ =
    raise-macneille-real-ℚ l (rational-ℕ 2)

  is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
    is-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-levy-sequence-macneille-ℝ)
      ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ)
  is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ (S , _) =
    leq-raise-macneille-real-ℚ
      ( dyadic-sum-bounded-sequence-bool S)
      ( rational-ℕ 2)
      ( leq-two-dyadic-sum-bounded-sequence-bool S)

  has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
    Σ (macneille-ℝ l)
      ( is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ))
  has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ =
    ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ ,
      is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ)
```

```agda
  endomap-levy-sequence-macneille-ℝ :
    macneille-ℝ l
  endomap-levy-sequence-macneille-ℝ =
    least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ)
      ( family-of-elements-levy-sequence-macneille-ℝ)
      ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ)
      ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ)

  abstract
    is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ :
      is-least-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ)
        ( endomap-levy-sequence-macneille-ℝ)
    is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ =
      is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ)
        ( family-of-elements-levy-sequence-macneille-ℝ)
        ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ)
        ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ)

  abstract
    is-least-upper-bound-family-of-elements-at-level-endomap-levy-sequence-macneille-ℝ :
      is-least-upper-bound-family-of-elements-at-level-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ)
        ( endomap-levy-sequence-macneille-ℝ)
    is-least-upper-bound-family-of-elements-at-level-endomap-levy-sequence-macneille-ℝ =
      is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ
```

```agda
is-levy-admissible-leq-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  (S : bounded-sequence-bool) →
  is-levy-admissible-bounded-sequence-bool f x S →
  is-levy-admissible-bounded-sequence-bool f y S
is-levy-admissible-leq-bounded-sequence-bool
  f x y x≤y S H m m∈S y≤fm =
  H m m∈S (transitive-leq-macneille-ℝ x y (f m) y≤fm x≤y)

abstract
  is-increasing-endomap-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-increasing-endomap-macneille-ℝ (endomap-levy-sequence-macneille-ℝ f)
  is-increasing-endomap-levy-sequence-macneille-ℝ f x y x≤y =
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
      ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f x)
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)
      ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)
      ( endomap-levy-sequence-macneille-ℝ f y)
      ( λ (S , adm-S) →
        is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( S , is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S))
```

## Adjoining indices to boolean predicates on ℕ

Given an index $n$ and a boolean predicate $χ$ bounded by $k$, we can adjoin $n$
to $χ$ obtain a new bounded boolean predicate that is bounded at $k + n + 1$.
For this formalization, we prefer this bound over $\max\{k, n+1\}$ since it
avoids case splitting on $n < k$.

If $\{n\}$ and $χ$ are admissible at $x$, then so is the adjoined predicate.

```agda
adjoin-index-bounded-sequence-bool :
  bounded-sequence-bool → ℕ → bounded-sequence-bool
adjoin-index-bounded-sequence-bool (k , χ , adm-χ) n =
  ( k +ℕ succ-ℕ n ,
    force-true-at-sequence-bool χ n ,
    λ m n+k≤m →
    is-false-force-true-at-sequence-bool χ n m
      ( λ p →
        neq-le-ℕ
          ( concatenate-le-leq-ℕ
            { x = n}
            { y = k +ℕ succ-ℕ n}
            { z = m}
            ( concatenate-le-leq-ℕ
              { x = n}
              { y = succ-ℕ n}
              { z = k +ℕ succ-ℕ n}
              ( succ-le-ℕ n)
              ( leq-add-ℕ' (succ-ℕ n) k))
            ( n+k≤m))
          ( inv p))
      ( adm-χ
        ( m)
        ( transitive-leq-ℕ k (k +ℕ succ-ℕ n) m n+k≤m (leq-add-ℕ k (succ-ℕ n)))))

is-levy-admissible-adjoin-index-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (n : ℕ) (S : bounded-sequence-bool) →
  ( (m : ℕ) → is-true (pr1 (pr2 S) m) → ¬ leq-macneille-ℝ y (f m)) →
  ¬ leq-macneille-ℝ y (f n) →
  is-levy-admissible-bounded-sequence-bool f y
    ( adjoin-index-bounded-sequence-bool S n)
is-levy-admissible-adjoin-index-bounded-sequence-bool
  f y n S adm-S not-y≤fn m m∈extend-S =
  rec-coproduct
    ( λ m=n → inv-tr (λ t → ¬ leq-macneille-ℝ y (f t)) m=n not-y≤fn)
    ( adm-S m)
    ( is-true-force-true-at-sequence-bool (pr1 (pr2 S)) n m m∈extend-S)
```

## Sum estimates when adjoining indices to bounded boolean predicates

We compare the dyadic sum on $χ$ and the dyadic sum on $n$ adjoined to $χ$,
$χ'$. We obtain

$$
∑_{i < k} χ(i)2⁻ⁱ ≤ ∑_{j < k + n + 1} χ'(j)2⁻ʲ,
$$

and, when $χ(n)$ is false, the refined inequality

$$
∑_{i < k} χ(i)2⁻ⁱ + 2⁻ⁿ ≤ ∑_{j < k + n + 1} χ'(j)2⁻ʲ.
$$

```agda
module _
  (n : ℕ) (S@(k , χ , _) : bounded-sequence-bool)
  where

  summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool i =
    summand-levy-sequence-macneille-ℝ (nat-Fin k i) (χ (nat-Fin k i))

  summand-fin-sequence-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  summand-fin-sequence-adjoin-index-bounded-sequence-bool i =
    summand-levy-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool i =
    summand-levy-sequence-macneille-ℝ
      ( nat-Fin k i)
      ( force-true-at-sequence-bool χ n (nat-Fin k i))

  summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool :
    Fin (succ-ℕ n) → ℚ
  summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool =
    summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
    inr-coproduct-Fin k (succ-ℕ n)

  abstract
    compute-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool :
      (i : Fin k) →
      summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool
        ( i) ＝
      summand-fin-sequence-adjoin-index-bounded-sequence-bool
        ( inl-coproduct-Fin k (succ-ℕ n) i)
    compute-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool
      i =
      ap
        ( λ m →
          summand-levy-sequence-macneille-ℝ m
            ( force-true-at-sequence-bool
            ( χ)
            ( n)
            ( m)))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))

    leq-old-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool :
      (i : Fin k) →
      leq-ℚ
        ( summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool i)
        ( summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool
          ( i))
    leq-old-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool
      i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool i)
            ( summand-levy-sequence-macneille-ℝ
              ( nat-Fin k i)
              ( force-true-at-sequence-bool χ n (nat-Fin k i))))
        ( λ p →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( summand-levy-sequence-macneille-ℝ (nat-Fin k i))
                  ( eq-force-true-at-eq-sequence-bool χ n (nat-Fin k i) p))))
            ( ind-bool
              ( λ b →
                leq-ℚ
                  ( summand-levy-sequence-macneille-ℝ (nat-Fin k i) b)
                  ( weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
              ( refl-leq-ℚ (weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
              ( leq-zero-weight-levy-sequence-macneille-ℝ (nat-Fin k i))
              ( χ (nat-Fin k i))))
        ( λ q →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( summand-levy-sequence-macneille-ℝ (nat-Fin k i))
                  ( eq-force-true-at-neq-sequence-bool χ n (nat-Fin k i) q))))
            ( refl-leq-ℚ _))
        ( has-decidable-equality-ℕ (nat-Fin k i) n)

    leq-zero-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool i)
    leq-zero-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( summand-levy-sequence-macneille-ℝ
              ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i))
              ( b)))
        ( leq-zero-weight-levy-sequence-macneille-ℝ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-at-sequence-bool χ n
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    leq-zero-sum-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( zero-ℚ)
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool))
    leq-zero-sum-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( λ _ → zero-ℚ)
          ( summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool)
          ( leq-zero-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool))
        ( leq-eq-ℚ (inv (eq-sum-zero-fin-sequence-ℚ (succ-ℕ n))))

    eq-sum-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool :
      sum-fin-sequence-ℚ k
        ( summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool) ＝
      sum-fin-sequence-ℚ k
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n))
    eq-sum-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( compute-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool))

  leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-extend-true-sequence-macneille-ℝ :
    leq-ℚ
      ( sum-fin-sequence-ℚ k summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool)
      ( sum-fin-sequence-ℚ k
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n)))
  leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-extend-true-sequence-macneille-ℝ =
    transitive-leq-ℚ _ _ _
      ( leq-eq-ℚ
        ( eq-sum-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool))
      ( preserves-leq-sum-fin-sequence-ℚ k
        ( summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool)
        ( summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool)
        ( leq-old-summand-inl-fin-sequence-adjoin-index-bounded-sequence-bool))

  leq-sum-inl-extended-fin-sequence-sum-summand-fin-sequence-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( sum-fin-sequence-ℚ k
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n)))
      ( sum-fin-sequence-ℚ
        ( k +ℕ succ-ℕ n)
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool))
  leq-sum-inl-extended-fin-sequence-sum-summand-fin-sequence-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-eq-ℚ
        ( inv
          ( split-sum-fin-sequence-ℚ k
            ( succ-ℕ n)
            ( summand-fin-sequence-adjoin-index-bounded-sequence-bool))))
      ( transitive-leq-ℚ _ _ _
        ( preserves-leq-right-add-ℚ
          ( sum-fin-sequence-ℚ k
            ( summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
              inl-coproduct-Fin k (succ-ℕ n)))
          ( zero-ℚ)
          ( sum-fin-sequence-ℚ
            ( succ-ℕ n)
            ( summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool))
          ( leq-zero-sum-summand-inr-fin-sequence-adjoin-index-bounded-sequence-bool))
        ( leq-eq-ℚ
          ( inv
            ( right-unit-law-add-ℚ
              ( sum-fin-sequence-ℚ k
                ( summand-fin-sequence-adjoin-index-bounded-sequence-bool ∘
                  inl-coproduct-Fin k (succ-ℕ n)))))))

  leq-sum-levy-base-index-map-ℕ-sum-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( dyadic-sum-bounded-sequence-bool S)
      ( dyadic-sum-bounded-sequence-bool
        ( adjoin-index-bounded-sequence-bool S n))
  leq-sum-levy-base-index-map-ℕ-sum-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-sum-inl-extended-fin-sequence-sum-summand-fin-sequence-adjoin-index-bounded-sequence-bool)
      ( leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-extend-true-sequence-macneille-ℝ)

  old-extended-fin-sequence-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  old-extended-fin-sequence-bounded-sequence-bool i =
    summand-levy-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( χ (nat-Fin (k +ℕ succ-ℕ n) i))

  inl-old-extended-fin-sequence-bounded-sequence-bool :
    Fin k → ℚ
  inl-old-extended-fin-sequence-bounded-sequence-bool =
    old-extended-fin-sequence-bounded-sequence-bool ∘
    inl-coproduct-Fin k (succ-ℕ n)

  inr-old-extended-fin-sequence-bounded-sequence-bool :
    Fin (succ-ℕ n) → ℚ
  inr-old-extended-fin-sequence-bounded-sequence-bool =
    old-extended-fin-sequence-bounded-sequence-bool ∘
    inr-coproduct-Fin k (succ-ℕ n)

  delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ :
    (m : ℕ) → is-decidable (m ＝ n) → ℚ
  delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ
    m =
    rec-coproduct (λ _ → weight-levy-sequence-macneille-ℝ n) (λ _ → zero-ℚ)

  delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ :
    Fin (k +ℕ succ-ℕ n) → ℚ
  delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ i =
    delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    eq-old-fin-sequence-inl-old-extended-fin-sequence-bounded-sequence-bool :
      (i : Fin k) →
      summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool i ＝
      inl-old-extended-fin-sequence-bounded-sequence-bool i
    eq-old-fin-sequence-inl-old-extended-fin-sequence-bounded-sequence-bool
      i =
      ap
        ( λ m → summand-levy-sequence-macneille-ℝ m (χ m))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))

    leq-zero-inr-old-extended-fin-sequence-bounded-sequence-bool :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( inr-old-extended-fin-sequence-bounded-sequence-bool i)
    leq-zero-inr-old-extended-fin-sequence-bounded-sequence-bool
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( summand-levy-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                ( inr-coproduct-Fin k (succ-ℕ n) i))
              ( b)))
        ( leq-zero-weight-levy-sequence-macneille-ℝ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( χ (nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-bounded-sequence-bool :
      sum-fin-sequence-ℚ k
        ( summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool) ＝
      sum-fin-sequence-ℚ k inl-old-extended-fin-sequence-bounded-sequence-bool
    eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-bounded-sequence-bool =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( eq-old-fin-sequence-inl-old-extended-fin-sequence-bounded-sequence-bool))

    leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-bounded-sequence-bool :
      leq-ℚ
        ( sum-fin-sequence-ℚ k
          ( summand-underlying-fin-sequence-adjoin-index-bounded-sequence-bool))
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( old-extended-fin-sequence-bounded-sequence-bool))
    leq-zero-sum-inr-old-extended-fin-sequence-bounded-sequence-bool :
      leq-ℚ
        ( zero-ℚ)
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( inr-old-extended-fin-sequence-bounded-sequence-bool))
    leq-zero-sum-inr-old-extended-fin-sequence-bounded-sequence-bool =
      leq-zero-sum-fin-sequence-ℚ
        ( succ-ℕ n)
        ( inr-old-extended-fin-sequence-bounded-sequence-bool)
        ( leq-zero-inr-old-extended-fin-sequence-bounded-sequence-bool)

    leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( inv
              ( split-sum-fin-sequence-ℚ
                ( k)
                ( succ-ℕ n)
                ( old-extended-fin-sequence-bounded-sequence-bool))))
          ( transitive-leq-ℚ _ _ _
            ( preserves-leq-right-add-ℚ
              ( sum-fin-sequence-ℚ k
                ( inl-old-extended-fin-sequence-bounded-sequence-bool))
              ( zero-ℚ)
              ( sum-fin-sequence-ℚ
                ( succ-ℕ n)
                ( inr-old-extended-fin-sequence-bounded-sequence-bool))
              ( leq-zero-sum-inr-old-extended-fin-sequence-bounded-sequence-bool))
            ( leq-eq-ℚ
              ( inv
                ( right-unit-law-add-ℚ
                  ( sum-fin-sequence-ℚ k
                    ( inl-old-extended-fin-sequence-bounded-sequence-bool)))))))
        ( leq-eq-ℚ
          ( eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-bounded-sequence-bool))

    eq-delta-fin-sequence-index-eq-levy-base-index-extend-true-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
      delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ i ＝
      weight-levy-sequence-macneille-ℝ n
    eq-delta-fin-sequence-index-eq-levy-base-index-extend-true-sequence-macneille-ℝ
      i =
      ind-coproduct
        ( λ d →
          nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
          delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ
            ( nat-Fin (k +ℕ succ-ℕ n) i)
            ( d) ＝
          weight-levy-sequence-macneille-ℝ n)
        ( λ _ _ → refl)
        ( λ q p' → ex-falso (q p'))
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    eq-delta-fin-sequence-selected-index-levy-base-index-extend-true-sequence-macneille-ℝ :
      delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ
        ( mod-succ-ℕ (k +ℕ n) n) ＝
      weight-levy-sequence-macneille-ℝ n
    eq-delta-fin-sequence-selected-index-levy-base-index-extend-true-sequence-macneille-ℝ
      =
      eq-delta-fin-sequence-index-eq-levy-base-index-extend-true-sequence-macneille-ℝ
        ( mod-succ-ℕ (k +ℕ n) n)
        ( eq-nat-fin-mod-add-succ-ℕ k n)

    eq-old-extended-fin-sequence-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      old-extended-fin-sequence-bounded-sequence-bool i ＝
      summand-levy-sequence-macneille-ℝ
        ( nat-Fin (k +ℕ succ-ℕ n) i)
        ( χ (nat-Fin (k +ℕ succ-ℕ n) i))
    eq-old-extended-fin-sequence-index-bounded-sequence-bool i =
      refl

    leq-zero-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ i)
    leq-zero-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ i
      =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( zero-ℚ)
            ( delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ
              ( nat-Fin (k +ℕ succ-ℕ n) i)
              ( d)))
        ( λ _ → leq-zero-weight-levy-sequence-macneille-ℝ n)
        ( λ _ → refl-leq-ℚ zero-ℚ)
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    leq-weight-sum-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ :
      leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ))
    leq-weight-sum-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ =
      transitive-leq-ℚ _ _ _
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ)
          ( leq-zero-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ)
          ( mod-succ-ℕ (k +ℕ n) n))
        ( leq-eq-ℚ
          ( inv
            ( eq-delta-fin-sequence-selected-index-levy-base-index-extend-true-sequence-macneille-ℝ)))

    leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool :
      is-false (χ n) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( old-extended-fin-sequence-bounded-sequence-bool i +ℚ
          delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ i)
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool
          ( i))
    leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool-from-decidable :
      (χn=false : is-false (χ n)) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      (d : is-decidable (nat-Fin (k +ℕ succ-ℕ n) i ＝ n)) →
      leq-ℚ
        ( old-extended-fin-sequence-bounded-sequence-bool i +ℚ
          delta-from-decidable-equality-index-levy-base-index-extend-true-sequence-macneille-ℝ
            ( nat-Fin (k +ℕ succ-ℕ n) i)
            ( d))
        ( summand-levy-sequence-macneille-ℝ
          ( nat-Fin (k +ℕ succ-ℕ n) i)
          ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i)))
    leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool-from-decidable
      χn=false i (inl p) =
      transitive-leq-ℚ _ _ _
        ( leq-eq-ℚ
          ( inv
            ( ( ap
                ( summand-levy-sequence-macneille-ℝ
                  ( nat-Fin (k +ℕ succ-ℕ n) i))
                ( eq-force-true-at-eq-sequence-bool χ n
                  ( nat-Fin (k +ℕ succ-ℕ n) i)
                  ( p))) ∙
              ( ap weight-levy-sequence-macneille-ℝ p))))
        ( transitive-leq-ℚ _ _ _
          ( ind-bool
            ( λ b →
              is-false b →
              leq-ℚ
                ( (summand-levy-sequence-macneille-ℝ n b) +ℚ
                  ( weight-levy-sequence-macneille-ℝ n))
                ( weight-levy-sequence-macneille-ℝ n))
            ( λ ())
            ( λ _ →
              leq-eq-ℚ
                ( left-unit-law-add-ℚ (weight-levy-sequence-macneille-ℝ n)))
            ( χ n)
            ( χn=false))
          ( leq-eq-ℚ
            ( ap
              ( λ m →
                ( summand-levy-sequence-macneille-ℝ m (χ m)) +ℚ
                ( weight-levy-sequence-macneille-ℝ n))
              ( p))))
    leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool-from-decidable
      χn=false i (inr q) =
      transitive-leq-ℚ _ _ _
        ( leq-eq-ℚ
          ( inv
            ( ap
              ( summand-levy-sequence-macneille-ℝ (nat-Fin (k +ℕ succ-ℕ n) i))
              ( eq-force-true-at-neq-sequence-bool χ n
                ( nat-Fin (k +ℕ succ-ℕ n) i)
                ( q)))))
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( right-unit-law-add-ℚ
              ( old-extended-fin-sequence-bounded-sequence-bool i)))
          ( refl-leq-ℚ _))
    leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool
      χn=false i =
      leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool-from-decidable
        ( χn=false)
        ( i)
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-adjoin-index-bounded-sequence-bool :
      is-false (χ n) →
      leq-ℚ
        ( dyadic-sum-bounded-sequence-bool S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-adjoin-index-bounded-sequence-bool
      χn=false =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( λ i →
            old-extended-fin-sequence-bounded-sequence-bool i +ℚ
            delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ
              ( i))
          ( summand-fin-sequence-adjoin-index-bounded-sequence-bool)
          ( leq-old-extended-add-delta-summand-fin-sequence-adjoin-index-bounded-sequence-bool
            ( χn=false)))
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( interchange-add-sum-fin-sequence-ℚ
              ( k +ℕ succ-ℕ n)
              ( old-extended-fin-sequence-bounded-sequence-bool)
              ( delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ)))
          ( preserves-leq-add-ℚ
            ( leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-bounded-sequence-bool)
            ( leq-weight-sum-delta-fin-sequence-levy-base-index-extend-true-sequence-macneille-ℝ)))
```

## Extended dyadic sums

The previous rational inequalities are now transported into $ℝₘ$ through the
canonical rational inclusion. Hence extending an index does not decrease the
corresponding family element. After monotone transport of admissibility from $x$
to $y$, we obtain the comparison between the old element at $x$ and the extended
element at $y$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-family-element-levy-base-index-map-ℕ-family-element-adjoin-index-bounded-sequence-bool :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ f x (S , adm-S))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( not-y≤fn)))
    leq-family-element-levy-base-index-map-ℕ-family-element-adjoin-index-bounded-sequence-bool
      n S x≤y adm-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-bounded-sequence-bool S)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-sum-levy-base-index-map-ℕ-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))
```

## Weight bounds for extended sums

Here we isolate the distinguished term $2⁻ⁿ$ inside the extended finite sum. The
index `iₙ` is chosen so that `nat-Fin ... iₙ ＝ n`. Nonnegativity of all
summands then implies

$$
2⁻ⁿ ≤ ∑_{j < k+n+1} χ'(j)2⁻ʲ.
$$

```agda
module _
  (n : ℕ) (S@(k , χ , _) : bounded-sequence-bool)
  where

  summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs :
    Fin (k +ℕ succ-ℕ n) → ℚ
  summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs i =
    summand-levy-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  abstract
    eq-selected-value-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs :
      summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs
        ( mod-succ-ℕ (k +ℕ n) n) ＝
      weight-levy-sequence-macneille-ℝ n
    eq-selected-value-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs =
      ap
        ( λ m →
          summand-levy-sequence-macneille-ℝ m
            ( force-true-at-sequence-bool χ n m))
        ( eq-nat-fin-mod-add-succ-ℕ k n) ∙
      ( ind-bool
        ( λ b →
          is-true b →
          summand-levy-sequence-macneille-ℝ n b ＝
          weight-levy-sequence-macneille-ℝ n)
        ( λ _ → refl)
        ( λ ())
        ( force-true-at-sequence-bool χ n n)
        ( is-true-force-true-at-self-sequence-bool χ n))

    leq-zero-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( zero-ℚ)
        ( summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs i)
    leq-zero-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( summand-levy-sequence-macneille-ℝ (nat-Fin (k +ℕ succ-ℕ n) i) b))
        ( leq-zero-weight-levy-sequence-macneille-ℝ (nat-Fin (k +ℕ succ-ℕ n) i))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  abstract
    leq-weight-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-weight-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs)
          ( leq-zero-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs)
          ( mod-succ-ℕ (k +ℕ n) n))
        ( leq-eq-ℚ
          ( inv
            ( eq-selected-value-summand-fin-sequence-adjoin-index-bounded-sequence-bool-wfs)))
```

## Weight bounds for extended family elements

The inequality on extended sums is pushed forward to MacNeille reals:

$$
\text{embedded }2⁻ⁿ ≤ family(\text{extended bounded selector}).
$$

This lemma is later combined with upper-bound transport to extend a translated
upper bound at the least upper bound point.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l)
  where

  abstract
    leq-weight-levy-map-ℕ-family-element-adjoin-index-bounded-sequence-bool :
      (n : ℕ) (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f y S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( adm-S)
              ( not-y≤fn)))
    leq-weight-levy-map-ℕ-family-element-adjoin-index-bounded-sequence-bool
      n S adm-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-weight-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))
```

## Admissibility at image indices

If $f(n) = x$, admissibility at $x$ implies that $n$ cannot be selected.

```agda
abstract
  is-false-admissible-index-image-bounded-sequence-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) (n : ℕ) →
    f n ＝ x →
    (S : bounded-sequence-bool) →
    is-levy-admissible-bounded-sequence-bool f x S →
    is-false (pr1 (pr2 S) n)
  is-false-admissible-index-image-bounded-sequence-bool
    f x n fn=x (k , (χ , adm-χ)) adm-S =
    is-false-is-not-true
      ( χ n)
      ( λ n∈S →
        adm-S n n∈S
          ( tr
            ( leq-macneille-ℝ x)
            ( inv fn=x)
            ( refl-leq-macneille-ℝ x)))
```

## Adding extended weights

Combining “$n$ was unselected” with the extension-sum estimate yields

$$
∑_{i < k} χ(i)2⁻ⁱ + 2⁻ⁿ ≤ ∑_{j < k+n+1} χ'(j)2⁻ʲ.
$$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-adjoin-index-bounded-sequence-bool :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-adjoin-index-bounded-sequence-bool
      n fn=x x≤y S adm-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-bounded-sequence-bool S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S)
          ( is-false-admissible-index-image-bounded-sequence-bool
            ( f)
            ( x)
            ( n)
            ( fn=x)
            ( S)
            ( adm-S)))

    leq-add-sum-levy-base-index-map-ℕ-weight-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-add-sum-levy-base-index-map-ℕ-weight-endomap-levy-sequence-macneille-ℝ
      n fn=x x≤y S adm-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-family-element-adjoin-index-bounded-sequence-bool
          ( n)
          ( fn=x)
          ( x≤y)
          ( S)
          ( adm-S)
          ( not-y≤fn))
```

## Extended upper-bound transport

This section turns the local extension inequalities into a global statement at
the least upper bound $x₀$ of the self-admissible family. The crucial step is a
double-negation argument: if the extended bounded selector were not $≤ x₀$, then
it would itself be self-admissible, contradicting maximality of $x₀$ as least
upper bound. After elimination of double negation on rational-left inequalities,
one obtains

$$
x₀ + 2⁻ⁿ ≤ x₀
$$

whenever $f(n) = x₀$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-extend-true-map-ℕ-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ f x (S , adm-S))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-extend-true-map-ℕ-endomap-levy-sequence-macneille-ℝ
      n S x≤y adm-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ f x (S , adm-S))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( leq-family-element-levy-base-index-map-ℕ-family-element-adjoin-index-bounded-sequence-bool
          ( f)
          ( x)
          ( y)
          ( n)
          ( S)
          ( x≤y)
          ( adm-S)
          ( not-y≤fn))

    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-extend-true-map-ℕ-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( weight-levy-sequence-macneille-ℝ n))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-extend-true-map-ℕ-endomap-levy-sequence-macneille-ℝ
      n S x≤y adm-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y)
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool
              ( f)
              ( y)
              ( n)
              ( S)
              ( is-levy-admissible-leq-bounded-sequence-bool f x y
                ( x≤y)
                ( S)
                ( adm-S))
              ( not-y≤fn)))
        ( leq-weight-levy-map-ℕ-family-element-adjoin-index-bounded-sequence-bool
          ( f)
          ( y)
          ( n)
          ( S)
          ( is-levy-admissible-leq-bounded-sequence-bool f x y
            ( x≤y)
            ( S)
            ( adm-S))
          ( not-y≤fn))
```

## Strict positivity of weights

We record that each dyadic weight $2⁻ⁿ$ is nonnegative (indeed positive). This
is the order-theoretic ingredient needed to contradict $x₀ + 2⁻ⁿ ≤ x₀$ in the
final step.

```agda
abstract
  le-zero-weight-levy-map-ℕ-ℚ :
    (n : ℕ) → le-ℚ zero-ℚ (weight-levy-sequence-macneille-ℝ n)
  le-zero-weight-levy-map-ℕ-ℚ n =
    le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺)

  le-raise-zero-weight-levy-sequence-macneille-ℝ :
    {l : Level} (n : ℕ) →
    le-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-real-ℚ l (weight-levy-sequence-macneille-ℝ n))
  le-raise-zero-weight-levy-sequence-macneille-ℝ {l} n =
    le-raise-macneille-real-ℚ
      ( zero-ℚ)
      ( weight-levy-sequence-macneille-ℝ n)
      ( le-zero-weight-levy-map-ℕ-ℚ n)
```

## Postfixpoints of the levy endomap

From the estimates above, $g(x) ≤ 2$ for all $x$, and $0$ is a postfixpoint.
Therefore the family of postfixpoints is inhabited and upper-bounded, so it has
a least upper bound; equivalently we obtain a greatest postfixpoint for $g$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  where

  abstract
    leq-two-endomap-levy-sequence-macneille-ℝ :
      (x : macneille-ℝ l) →
      leq-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f x)
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
    leq-two-endomap-levy-sequence-macneille-ℝ x =
      leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
        ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f x)
        ( family-of-elements-levy-sequence-macneille-ℝ f x)
        ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)
        ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
        ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)

    is-postfixpoint-zero-endomap-levy-sequence-macneille-ℝ :
      is-postfixpoint-endomap-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f)
        ( raise-zero-macneille-ℝ l)
    is-postfixpoint-zero-endomap-levy-sequence-macneille-ℝ =
      is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f
          ( raise-zero-macneille-ℝ l))
        ( family-of-elements-levy-sequence-macneille-ℝ f
          ( raise-zero-macneille-ℝ l))
        ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f
          ( raise-zero-macneille-ℝ l))
        ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f
          ( raise-zero-macneille-ℝ l))
        ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) ,
          ( λ _ ()))

  is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-macneille-ℝ :
    is-inhabited
      ( indexing-type-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f))
  is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-macneille-ℝ =
    unit-trunc-Prop
      ( raise-zero-macneille-ℝ l ,
        is-postfixpoint-zero-endomap-levy-sequence-macneille-ℝ)

  upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ : macneille-ℝ l
  upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ =
    raise-macneille-real-ℚ l (rational-ℕ 2)

  abstract
    is-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ :
      is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-postfixpoints-endomap-macneille-ℝ
          ( endomap-levy-sequence-macneille-ℝ f))
        ( upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ)
    is-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ (x , x≤gx) =
      transitive-leq-macneille-ℝ
        ( x)
        ( endomap-levy-sequence-macneille-ℝ f x)
        ( upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ)
        ( leq-two-endomap-levy-sequence-macneille-ℝ x)
        ( x≤gx)

  has-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ :
    Σ (macneille-ℝ l)
      ( is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-postfixpoints-endomap-macneille-ℝ
          ( endomap-levy-sequence-macneille-ℝ f)))
  has-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ =
    ( upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ ,
      is-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ)

  has-least-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ :
    has-least-upper-bound-family-of-elements-macneille-ℝ
      lzero
      ( family-of-elements-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f))
  has-least-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ =
    has-least-upper-bound-inhabited-upper-bounded-family-of-elements-macneille-ℝ
      ( is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-macneille-ℝ)
      ( family-of-elements-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f))
      ( upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ)
      ( is-upper-bound-postfixpoints-endomap-levy-sequence-macneille-ℝ)
```

## Finite Levy escaping image argument

Instead of quantifying over all postfixpoints directly, we now specialize to
finite self-admissible bounded selectors, i.e., bounded selectors admissible at
their own sum. Their family again has an inhabited bounded index type, so we may
define

$$
x₀ ≔ sup\{\,\text{family element of }(k,χ,outside) | (k,χ,outside)\text{ is self-admissible}\,\}.
$$

The remaining argument shows $x₀ ∉ im(f)$.

```agda
is-self-admissible-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  bounded-sequence-bool → UU l
is-self-admissible-bounded-sequence-bool {l} f S =
  is-levy-admissible-bounded-sequence-bool f
    ( raise-macneille-real-ℚ l
      ( dyadic-sum-bounded-sequence-bool S))
    ( S)

indexing-type-self-admissible-levy-family-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) → UU l
indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f =
  Σ bounded-sequence-bool
    ( is-self-admissible-bounded-sequence-bool f)

family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f →
  macneille-ℝ l
family-of-elements-self-admissible-levy-sequence-macneille-ℝ {l} _ (S , _) =
  raise-macneille-real-ℚ l (dyadic-sum-bounded-sequence-bool S)

abstract
  is-inhabited-indexing-type-self-admissible-levy-family-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-inhabited (indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f)
  is-inhabited-indexing-type-self-admissible-levy-family-sequence-macneille-ℝ
    _ =
    unit-trunc-Prop
      ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) , λ _ ())

upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) → macneille-ℝ l
upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ {l} _ =
  raise-macneille-real-ℚ l (rational-ℕ 2)

abstract
  is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
  is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ
    {l} f (S , _) =
    leq-raise-macneille-real-ℚ
      ( dyadic-sum-bounded-sequence-bool S)
      ( rational-ℕ 2)
      ( leq-two-dyadic-sum-bounded-sequence-bool S)

has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l)
    ( is-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f =
  ( upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f ,
    is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)

point-self-admissible-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) → macneille-ℝ l
point-self-admissible-levy-sequence-macneille-ℝ f =
  least-upper-bound-inhabited-bounded-family-macneille-ℝ
    ( is-inhabited-indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f)
    ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
    ( upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
    ( is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)

abstract
  is-least-upper-bound-family-of-elements-point-self-admissible-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( point-self-admissible-levy-sequence-macneille-ℝ f)
  is-least-upper-bound-family-of-elements-point-self-admissible-levy-sequence-macneille-ℝ
    f =
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f)
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)

  leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    ( i : indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f) →
    leq-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f i)
      ( point-self-admissible-levy-sequence-macneille-ℝ f)
  leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ f =
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f)
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( is-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
```

### Contradiction at the least upper bound

Assume $f(n) = x₀$. Then admissibility extends $n$ to be unselected in every
self-admissible bounded selector $S$, so extending $n$ contributes at least
$2⁻ⁿ$. Using least upper-bound transport under rational translation, we derive

$$
x₀ + 2⁻ⁿ ≤ x₀.
$$

Since $2⁻ⁿ ≥ 0$, this contradicts strict positivity. Hence $f(n) ≠ x₀$ for all
$n$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (let x0 = point-self-admissible-levy-sequence-macneille-ℝ f)
  where

  abstract
    leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ' :
      ( S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S))
        ( x0)
    leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ'
      S self-adm-S =
      leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ f
        ( S , self-adm-S)

    is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      is-false (pr1 (pr2 S) n)
    is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-adm-S =
      is-false-admissible-index-image-bounded-sequence-bool
        ( f)
        ( x0)
        ( n)
        ( fn=x0)
        ( S)
        ( is-levy-admissible-leq-bounded-sequence-bool f
          ( raise-macneille-real-ℚ l
            ( dyadic-sum-bounded-sequence-bool S))
          ( x0)
          ( leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ'
            ( S)
            ( self-adm-S))
          ( S)
          ( self-adm-S))

    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      leq-ℚ
        ( dyadic-sum-bounded-sequence-bool S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-adm-S =
      leq-add-sum-levy-base-index-map-ℕ-weight-sum-adjoin-index-bounded-sequence-bool
        ( n)
        ( S)
        ( is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ
          ( n)
          ( fn=x0)
          ( S)
          ( self-adm-S))

    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool
            ( adjoin-index-bounded-sequence-bool S n)))
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-adm-S =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-bounded-sequence-bool S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ
          n fn=x0 S self-adm-S)

  abstract
    leq-sum-levy-base-index-map-ℕ-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (S : bounded-sequence-bool) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool S))
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool
            ( adjoin-index-bounded-sequence-bool S n)))
    leq-sum-levy-base-index-map-ℕ-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n S =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-bounded-sequence-bool S)
        ( dyadic-sum-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-sum-levy-base-index-map-ℕ-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))

  abstract
    is-self-admissible-adjoin-index-bounded-sequence-bool-from-not-leq :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      ¬ leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool
            ( adjoin-index-bounded-sequence-bool S n)))
        ( x0) →
      is-self-admissible-bounded-sequence-bool f
        ( adjoin-index-bounded-sequence-bool S n)
    is-self-admissible-adjoin-index-bounded-sequence-bool-from-not-leq
      n fn=x0 S self-adm-S not-extend-S≤x0 =
      is-levy-admissible-adjoin-index-bounded-sequence-bool
        ( f)
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-bounded-sequence-bool
            ( adjoin-index-bounded-sequence-bool S n)))
        ( n)
        ( S)
        ( λ m m∈S sum-extend-S≤fm →
          self-adm-S m m∈S
            ( transitive-leq-macneille-ℝ
              ( raise-macneille-real-ℚ l
                ( dyadic-sum-bounded-sequence-bool S))
              ( raise-macneille-real-ℚ l
                ( dyadic-sum-bounded-sequence-bool
                  ( adjoin-index-bounded-sequence-bool S n)))
              ( f m)
              ( sum-extend-S≤fm)
              ( leq-sum-levy-base-index-map-ℕ-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
                ( n)
                ( S))))
        ( λ sum-extend-S≤fn →
          not-extend-S≤x0
            ( tr
              ( leq-macneille-ℝ
                  ( raise-macneille-real-ℚ l
                    ( dyadic-sum-bounded-sequence-bool
                      ( adjoin-index-bounded-sequence-bool S n))))
              ( fn=x0)
              ( sum-extend-S≤fn)))

    double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : bounded-sequence-bool) →
      is-self-admissible-bounded-sequence-bool f S →
      ¬¬
        ( leq-macneille-ℝ
          ( raise-macneille-real-ℚ l
            ( dyadic-sum-bounded-sequence-bool
              ( adjoin-index-bounded-sequence-bool S n)))
          ( x0))
    double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-adm-S not-extend-S≤x0 =
      not-extend-S≤x0
        ( leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ f
          ( adjoin-index-bounded-sequence-bool S n ,
            is-self-admissible-adjoin-index-bounded-sequence-bool-from-not-leq
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S)
              ( not-extend-S≤x0)))

  abstract
    leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : bounded-sequence-bool) →
      ( self-adm-S :
        is-self-admissible-bounded-sequence-bool f S) →
      leq-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( weight-levy-sequence-macneille-ℝ n)
          ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
          ( S , self-adm-S))
        ( x0)
    leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-adm-S =
      let
        extend-S≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-bounded-sequence-bool
                ( adjoin-index-bounded-sequence-bool S n)))
            ( x0)
        extend-S≤x0 =
          double-negation-elim-leq-left-raise-macneille-real-ℚ
            ( x0)
            ( dyadic-sum-bounded-sequence-bool
              ( adjoin-index-bounded-sequence-bool S n))
            ( double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S))

        add-sum-S+weight≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-bounded-sequence-bool S +ℚ
                weight-levy-sequence-macneille-ℝ n))
            ( x0)
        add-sum-S+weight≤x0 =
          transitive-leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-bounded-sequence-bool S +ℚ
                weight-levy-sequence-macneille-ℝ n))
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-bounded-sequence-bool
                ( adjoin-index-bounded-sequence-bool S n)))
            ( x0)
            ( extend-S≤x0)
            ( leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S))

        add-weight+sum-S≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( weight-levy-sequence-macneille-ℝ n +ℚ
                dyadic-sum-bounded-sequence-bool S))
            ( x0)
        add-weight+sum-S≤x0 =
          tr
            ( λ z → leq-macneille-ℝ z x0)
            ( ap
              ( raise-macneille-real-ℚ l)
              ( commutative-add-ℚ
                ( dyadic-sum-bounded-sequence-bool S)
                ( weight-levy-sequence-macneille-ℝ n)))
            ( add-sum-S+weight≤x0)
      in
        tr
          ( λ z → leq-macneille-ℝ z x0)
          ( inv
            ( eq-right-translate-raise-macneille-real-ℚ'
              ( weight-levy-sequence-macneille-ℝ n)
              ( dyadic-sum-bounded-sequence-bool S)))
          ( add-weight+sum-S≤x0)

    is-upper-bound-right-translate-family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      is-upper-bound-family-of-elements-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( weight-levy-sequence-macneille-ℝ n)
          ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
        ( x0)
    is-upper-bound-right-translate-family-of-elements-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 (S , self-adm-S) =
      leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ
        ( n)
        ( fn=x0)
        ( S)
        ( self-adm-S)

    leq-right-translate-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      leq-macneille-ℝ
        ( add-macneille-ℝ
          ( located-macneille-real-ℚ
            ( weight-levy-sequence-macneille-ℝ n))
          ( x0))
        ( x0)
    leq-right-translate-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 =
      forward-implication
        ( is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
          ( weight-levy-sequence-macneille-ℝ n)
          ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
          ( x0)
          ( is-least-upper-bound-family-of-elements-point-self-admissible-levy-sequence-macneille-ℝ
            ( f))
          ( x0))
        ( is-upper-bound-right-translate-family-of-elements-self-admissible-levy-sequence-macneille-ℝ
          ( n)
          ( fn=x0))

    not-in-image-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) → f n ≠ x0
    not-in-image-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 =
      not-leq-right-translate-positive-macneille-real-ℚ
        ( x0)
        ( weight-levy-sequence-macneille-ℝ n)
        ( le-zero-weight-levy-map-ℕ-ℚ n)
        ( leq-right-translate-point-self-admissible-levy-sequence-macneille-ℝ n
          ( fn=x0))
```

### Sequence-avoiding point

We have produced a sequence-avoiding point for a general $f$: a point $x₀$
together with a proof that every index $n$ satisfies $f(n) ≠ x₀$.

```agda
sequence-avoiding-point-levy-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
sequence-avoiding-point-levy-macneille-ℝ f =
  ( point-self-admissible-levy-sequence-macneille-ℝ f ,
    not-in-image-point-self-admissible-levy-sequence-macneille-ℝ f)
```

## References

{{#bibliography}}
