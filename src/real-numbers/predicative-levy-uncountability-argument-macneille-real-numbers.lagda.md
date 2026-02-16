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
$x : ℝₘ$, we will say a subset $S$ of $ℕ$ is _(Levy) $f$-admissible at_ $x$ if
$i ∈ S$ implies that $x ≰ f(i)$. In particular, this means elements of $S$ are
required to lie to the right of $x$ under $f$.

We assign to each subset $S$ the dyadic sum $∑_{i ∈ S}2⁻ⁱ$. This defines a
family of elements in $ℝₘ$ which is inhabited (take $S$ the empty subset) and
bounded above by $2$, since

$$
  ∑_{i ∈ S}2⁻ⁱ ≤ ∑_i 2⁻ⁱ = 2.
$$

Hence by
[order completeness of the MacNeille reals](real-numbers.least-upper-bounds-families-macneille-real-numbers.md)
it has a least upper bound. This defines an endomap $g : ℝₘ → ℝₘ$,

$$
  g(x) ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ finite and admissible at }x\}.
$$

Note that finite subsets can be encoded as bounded boolean predicates
$χ : ℕ → bool$ so this construction is predicative.

Next, fix an index $n$ and adjoin it to $S$. This extension preserves finiteness
and yields the inequality $∑_{i ∈ S}2⁻ⁱ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ$. If $n ∉ S$,
then we may refine this inequality to:

$$
  ∑_{i ∈ S}2⁻ⁱ + 2⁻ⁿ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ.
$$

Now restrict to _self-admissible_ finite subsets $S$, in the sense that $S$ is
admissible at its dyadic sum $∑_{i ∈ S}2⁻ⁱ$. From the collection of
self-admissible finite subsets we may form an inhabited bounded family of
MacNeille reals. Let

$$
  x₀ ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ is self-admissible finite subset}\},
$$

and assume for the sake of reaching a contradiction that $f(n) = x₀$. Then
$n ∉ S$ for any self-admissible finite subset $S$. Applying the extension
inequality and using the fact that $x₀$ is a least upper bound yields

$$
  x₀ + 2⁻ⁿ ≤ x₀.
$$

Which is absurd. Therefore $f(n) ≠ x₀$ for all $n$. ∎

## The dyadic sum of a bounded boolean predicate

Fix $f : ℕ → ℝₘ$ and $x : ℝₘ$. The type `bounded-sequence-bool` encodes bounded
boolean predicates `χ : ℕ → bool`

Hence admissible bounded boolean sequences represent finite sets of indices that
are extended to lie to the right of $x$ under $f$. Note, however, that they do
not form unique representations since the upper bound is not unique.

```agda
bounded-sequence-bool : UU lzero
bounded-sequence-bool =
  Σ ℕ (λ k → Σ (ℕ → bool) (λ χ → (m : ℕ) → leq-ℕ k m → is-false (χ m)))
```

Each included index $n$ contributes the dyadic coefficient $2⁻ⁿ = (½)ⁿ$. We
define the dyadic sum of $χ$ as $∑_{i < k} χ(i)2⁻ⁱ$.

```agda
power-two-neg-ℚ : ℕ → ℚ
power-two-neg-ℚ n =
  power-ℚ n one-half-ℚ

dyadic-summand-bool-ℚ : ℕ → bool → ℚ
dyadic-summand-bool-ℚ n =
  rec-bool (power-two-neg-ℚ n) zero-ℚ

dyadic-sum-ℚ-bounded-sequence-bool :
  bounded-sequence-bool → ℚ
dyadic-sum-ℚ-bounded-sequence-bool (k , χ , _) =
  sum-fin-sequence-ℚ k
    ( λ i → dyadic-summand-bool-ℚ (nat-Fin k i) (χ (nat-Fin k i)))

raise-dyadic-sum-ℝₘ-bounded-sequence-bool :
  (l : Level) → bounded-sequence-bool → macneille-ℝ l
raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S =
  raise-macneille-real-ℚ l (dyadic-sum-ℚ-bounded-sequence-bool S)

abstract
  leq-zero-power-two-neg-ℚ :
    (n : ℕ) → leq-ℚ zero-ℚ (power-two-neg-ℚ n)
  leq-zero-power-two-neg-ℚ n =
    leq-le-ℚ (le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺))

  leq-dyadic-summand-bool-ℚ :
    (n : ℕ) (b : bool) →
    leq-ℚ
      ( dyadic-summand-bool-ℚ n b)
      ( power-two-neg-ℚ n)
  leq-dyadic-summand-bool-ℚ n true =
    refl-leq-ℚ (power-two-neg-ℚ n)
  leq-dyadic-summand-bool-ℚ n false =
    leq-zero-power-two-neg-ℚ n
```

$$
  ∑_{i ∈ S}2⁻ⁱ ≤ ∑_{i < k}2⁻ⁱ ≤ 2
$$

```agda
  leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ :
    (S : bounded-sequence-bool) →
    leq-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( sum-fin-sequence-ℚ
        ( pr1 S)
        ( λ i → power-two-neg-ℚ (nat-Fin (pr1 S) i)))
  leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ (k , χ , _) =
    preserves-leq-sum-fin-sequence-ℚ
      ( k)
      ( λ i → dyadic-summand-bool-ℚ (nat-Fin k i) (χ (nat-Fin k i)))
      ( λ i → power-two-neg-ℚ (nat-Fin k i))
      ( λ i → leq-dyadic-summand-bool-ℚ (nat-Fin k i) (χ (nat-Fin k i)))

  eq-full-dyadic-sum-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    sum-fin-sequence-ℚ k (λ i → power-two-neg-ℚ (nat-Fin k i)) ＝
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
      ( sum-fin-sequence-ℚ k (λ i → power-two-neg-ℚ (nat-Fin k i)))
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
  leq-two-dyadic-sum-ℚ-bounded-sequence-bool (k , χ , adm-χ) =
    transitive-leq-ℚ _ _ _
      ( leq-two-full-dyadic-sum-ℚ-bounded-sequence-bool k)
      ( leq-dyadic-sum-bounded-sequence-bool-full-dyadic-sum-ℚ
        ( k , χ , adm-χ))
```

## Levy admissibility of boolean sequences and Levy's endomap

The results above establish that the family of dyadic sums over bounded boolean
sequences is inhabited and bounded, so we can define Levy’s endomap

$$
  g(x) ≔ \sup\{∑_{i ∈ S}2⁻ⁱ | S\text{ finite and }$f$\text{-admissible at }x\},
$$

where, as stated before, $S$ is $f$-admissible at $x$ if $m ∈ S$ implies
$x ≰ f(m)$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l)
  where

  is-levy-admissible-bounded-sequence-bool :
    bounded-sequence-bool → UU l
  is-levy-admissible-bounded-sequence-bool (k , χ , _) =
    (m : ℕ) → is-true (χ m) → ¬ leq-macneille-ℝ x (f m)

  levy-admissible-bounded-sequence-bool : UU l
  levy-admissible-bounded-sequence-bool =
    Σ (bounded-sequence-bool) (is-levy-admissible-bounded-sequence-bool)

  dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool :
    levy-admissible-bounded-sequence-bool →
    macneille-ℝ l
  dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool (S , _) =
    raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S

  point-levy-admissible-bounded-sequence-bool :
    levy-admissible-bounded-sequence-bool
  point-levy-admissible-bounded-sequence-bool =
    ((zero-ℕ , (λ _ → false) , (λ _ _ → refl)) , (λ _ ()))

  is-inhabited-levy-admissible-bounded-sequence-bool :
    is-inhabited levy-admissible-bounded-sequence-bool
  is-inhabited-levy-admissible-bounded-sequence-bool =
    unit-trunc-Prop point-levy-admissible-bounded-sequence-bool

  upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool :
    macneille-ℝ l
  upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool =
    raise-macneille-real-ℚ l (rational-ℕ 2)

  is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool :
    is-upper-bound-family-of-elements-macneille-ℝ
      ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
      ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
  is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool (S , _) =
    leq-raise-macneille-real-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( rational-ℕ 2)
      ( leq-two-dyadic-sum-ℚ-bounded-sequence-bool S)

  has-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool :
    Σ (macneille-ℝ l)
      ( is-upper-bound-family-of-elements-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool))
  has-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool =
    ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool ,
      is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
```

```agda
  endomap-levy-sequence-ℝₘ :
    macneille-ℝ l
  endomap-levy-sequence-ℝₘ =
    least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-admissible-bounded-sequence-bool)
      ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
      ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
      ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)

  abstract
    is-least-upper-bound-dyadic-sum-endomap-levy-sequence-ℝₘ :
      is-least-upper-bound-family-of-elements-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
        ( endomap-levy-sequence-ℝₘ)
    is-least-upper-bound-dyadic-sum-endomap-levy-sequence-ℝₘ =
      is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-levy-admissible-bounded-sequence-bool)
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
        ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool)
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
  is-increasing-endomap-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-increasing-endomap-macneille-ℝ (endomap-levy-sequence-ℝₘ f)
  is-increasing-endomap-levy-sequence-ℝₘ f x y x≤y =
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
      ( is-inhabited-levy-admissible-bounded-sequence-bool f x)
      ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
      ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
      ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
      ( endomap-levy-sequence-ℝₘ f y)
      ( λ (S , adm-S) →
        is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( S , is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S))
```

## Adjoining indices to boolean predicates on ℕ

Given an index $n$ and a boolean predicate $χ$ bounded by $k$, we can adjoin $n$
to $χ$ obtain a new bounded boolean predicate that is bounded at $k + n + 1$. We
could also have chosen the bound to be $\max\{k, n + 1\}$, but for the
formalization, we prefer the former as it avoids case splitting on whether
$n < k$.

If $χ$ and $\{n\}$ are admissible at $x$, then so is the extended predicate.

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

raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool :
  (l : Level) →
  bounded-sequence-bool →
  ℕ →
  macneille-ℝ l
raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n =
  raise-dyadic-sum-ℝₘ-bounded-sequence-bool l
    ( adjoin-index-bounded-sequence-bool S n)

is-levy-admissible-adjoin-index-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (n : ℕ) (S : bounded-sequence-bool) →
  is-levy-admissible-bounded-sequence-bool f y S →
  ¬ leq-macneille-ℝ y (f n) →
  is-levy-admissible-bounded-sequence-bool f y
    ( adjoin-index-bounded-sequence-bool S n)
is-levy-admissible-adjoin-index-bounded-sequence-bool
  f y n S adm-S y≰fn m m∈extend-S =
  rec-coproduct
    ( λ m=n → inv-tr (λ t → ¬ leq-macneille-ℝ y (f t)) m=n y≰fn)
    ( adm-S m)
    ( is-true-force-true-at-sequence-bool (pr1 (pr2 S)) n m m∈extend-S)

adjoin-index-levy-admissible-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (S : levy-admissible-bounded-sequence-bool f y) (n : ℕ) →
  ¬ leq-macneille-ℝ y (f n) →
  levy-admissible-bounded-sequence-bool f y
adjoin-index-levy-admissible-bounded-sequence-bool f y (S , adm-S) n y≰fn =
  ( adjoin-index-bounded-sequence-bool S n ,
    is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S adm-S y≰fn)
```

## Dyadic sum estimates when adjoining indices

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
  (n : ℕ) (S@(k , χ , _) : bounded-sequence-bool)
  where

  summand-underlying-finseq-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-underlying-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ (nat-Fin k i) (χ (nat-Fin k i))

  summand-finseq-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  summand-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  summand-inl-finseq-adjoin-index-bounded-sequence-bool :
    Fin k → ℚ
  summand-inl-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin k i)
      ( force-true-at-sequence-bool χ n (nat-Fin k i))

  summand-inr-finseq-adjoin-index-bounded-sequence-bool :
    Fin (succ-ℕ n) → ℚ
  summand-inr-finseq-adjoin-index-bounded-sequence-bool =
    summand-finseq-adjoin-index-bounded-sequence-bool ∘
    inr-coproduct-Fin k (succ-ℕ n)

  abstract
    compute-summand-inl-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin k) →
      summand-inl-finseq-adjoin-index-bounded-sequence-bool
        ( i) ＝
      summand-finseq-adjoin-index-bounded-sequence-bool
        ( inl-coproduct-Fin k (succ-ℕ n) i)
    compute-summand-inl-finseq-adjoin-index-bounded-sequence-bool
      i =
      ap
        ( λ m →
          dyadic-summand-bool-ℚ m
            ( force-true-at-sequence-bool
            ( χ)
            ( n)
            ( m)))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))

    leq-summand-underlying-inl-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin k) →
      leq-ℚ
        ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool i)
        ( summand-inl-finseq-adjoin-index-bounded-sequence-bool
          ( i))
    leq-summand-underlying-inl-finseq-adjoin-index-bounded-sequence-bool
      i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool i)
            ( dyadic-summand-bool-ℚ
              ( nat-Fin k i)
              ( force-true-at-sequence-bool χ n (nat-Fin k i))))
        ( λ p →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin k i))
                  ( eq-force-true-at-eq-sequence-bool χ n (nat-Fin k i) p))))
            ( ind-bool
              ( λ b →
                leq-ℚ
                  ( dyadic-summand-bool-ℚ (nat-Fin k i) b)
                  ( power-two-neg-ℚ (nat-Fin k i)))
              ( refl-leq-ℚ (power-two-neg-ℚ (nat-Fin k i)))
              ( leq-zero-power-two-neg-ℚ (nat-Fin k i))
              ( χ (nat-Fin k i))))
        ( λ q →
          transitive-leq-ℚ _ _ _
            ( leq-eq-ℚ
              ( inv
                ( ap
                  ( dyadic-summand-bool-ℚ (nat-Fin k i))
                  ( eq-force-true-at-neq-sequence-bool χ n (nat-Fin k i) q))))
            ( refl-leq-ℚ _))
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
        ( leq-zero-power-two-neg-ℚ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-at-sequence-bool χ n
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    leq-zero-sum-summand-inr-finseq-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( zero-ℚ)
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( summand-inr-finseq-adjoin-index-bounded-sequence-bool))
    leq-zero-sum-summand-inr-finseq-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( λ _ → zero-ℚ)
          ( summand-inr-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-zero-summand-inr-finseq-adjoin-index-bounded-sequence-bool))
        ( leq-eq-ℚ (inv (eq-sum-zero-fin-sequence-ℚ (succ-ℕ n))))

    eq-sum-summand-inl-finseq-adjoin-index-bounded-sequence-bool :
      sum-fin-sequence-ℚ k
        ( summand-inl-finseq-adjoin-index-bounded-sequence-bool) ＝
      sum-fin-sequence-ℚ k
        ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n))
    eq-sum-summand-inl-finseq-adjoin-index-bounded-sequence-bool =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( compute-summand-inl-finseq-adjoin-index-bounded-sequence-bool))

  leq-sum-underlying-finseq-sum-inl-extended-adjoin-index-bounded-sequence-bool :
    leq-ℚ
      ( sum-fin-sequence-ℚ k summand-underlying-finseq-adjoin-index-bounded-sequence-bool)
      ( sum-fin-sequence-ℚ k
        ( summand-finseq-adjoin-index-bounded-sequence-bool ∘
          inl-coproduct-Fin k (succ-ℕ n)))
  leq-sum-underlying-finseq-sum-inl-extended-adjoin-index-bounded-sequence-bool =
    transitive-leq-ℚ _ _ _
      ( leq-eq-ℚ
        ( eq-sum-summand-inl-finseq-adjoin-index-bounded-sequence-bool))
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
      ( χ (nat-Fin (k +ℕ succ-ℕ n) i))

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

  delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool :
    (m : ℕ) → is-decidable (m ＝ n) → ℚ
  delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool
    m =
    rec-coproduct (λ _ → power-two-neg-ℚ n) (λ _ → zero-ℚ)

  delta-finseq-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  delta-finseq-adjoin-index-bounded-sequence-bool i =
    delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool :
      (i : Fin k) →
      summand-underlying-finseq-adjoin-index-bounded-sequence-bool i ＝
      inl-underlying-extended-finseq-bounded-sequence-bool i
    eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool
      i =
      ap
        ( λ m → dyadic-summand-bool-ℚ m (χ m))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))

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
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                ( inr-coproduct-Fin k (succ-ℕ n) i))
              ( b)))
        ( leq-zero-power-two-neg-ℚ
          ( nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))
        ( refl-leq-ℚ zero-ℚ)
        ( χ (nat-Fin (k +ℕ succ-ℕ n) (inr-coproduct-Fin k (succ-ℕ n) i)))

    eq-sum-underlying-finseq-sum-inl-underlying-extended-finseq-bounded-sequence-bool :
      sum-fin-sequence-ℚ k
        ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool) ＝
      sum-fin-sequence-ℚ k inl-underlying-extended-finseq-bounded-sequence-bool
    eq-sum-underlying-finseq-sum-inl-underlying-extended-finseq-bounded-sequence-bool =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( eq-underlying-finseq-inl-underlying-extended-finseq-bounded-sequence-bool))

    leq-sum-underlying-finseq-sum-underlying-extended-finseq-bounded-sequence-bool :
      leq-ℚ
        ( sum-fin-sequence-ℚ k
          ( summand-underlying-finseq-adjoin-index-bounded-sequence-bool))
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( underlying-extended-finseq-bounded-sequence-bool))
    leq-zero-sum-inr-underlying-extended-finseq-bounded-sequence-bool :
      leq-ℚ
        ( zero-ℚ)
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( inr-underlying-extended-finseq-bounded-sequence-bool))
    leq-zero-sum-inr-underlying-extended-finseq-bounded-sequence-bool =
      leq-zero-sum-fin-sequence-ℚ
        ( succ-ℕ n)
        ( inr-underlying-extended-finseq-bounded-sequence-bool)
        ( leq-zero-inr-underlying-extended-finseq-bounded-sequence-bool)

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
              ( leq-zero-sum-inr-underlying-extended-finseq-bounded-sequence-bool))
            ( leq-eq-ℚ
              ( inv
                ( right-unit-law-add-ℚ
                  ( sum-fin-sequence-ℚ k
                    ( inl-underlying-extended-finseq-bounded-sequence-bool)))))))
        ( leq-eq-ℚ
          ( eq-sum-underlying-finseq-sum-inl-underlying-extended-finseq-bounded-sequence-bool))

    eq-delta-finseq-index-eq-adjoin-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
      delta-finseq-adjoin-index-bounded-sequence-bool i ＝
      power-two-neg-ℚ n
    eq-delta-finseq-index-eq-adjoin-index-bounded-sequence-bool
      i =
      ind-coproduct
        ( λ d →
          nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
          delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool
            ( nat-Fin (k +ℕ succ-ℕ n) i)
            ( d) ＝
          power-two-neg-ℚ n)
        ( λ _ _ → refl)
        ( λ q p' → ex-falso (q p'))
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    eq-delta-finseq-selected-index-adjoin-index-bounded-sequence-bool :
      delta-finseq-adjoin-index-bounded-sequence-bool
        ( mod-succ-ℕ (k +ℕ n) n) ＝
      power-two-neg-ℚ n
    eq-delta-finseq-selected-index-adjoin-index-bounded-sequence-bool
      =
      eq-delta-finseq-index-eq-adjoin-index-bounded-sequence-bool
        ( mod-succ-ℕ (k +ℕ n) n)
        ( eq-nat-fin-mod-add-succ-ℕ k n)

    eq-underlying-extended-finseq-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      underlying-extended-finseq-bounded-sequence-bool i ＝
      dyadic-summand-bool-ℚ
        ( nat-Fin (k +ℕ succ-ℕ n) i)
        ( χ (nat-Fin (k +ℕ succ-ℕ n) i))
    eq-underlying-extended-finseq-index-bounded-sequence-bool i =
      refl

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
            ( delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool
              ( nat-Fin (k +ℕ succ-ℕ n) i)
              ( d)))
        ( λ _ → leq-zero-power-two-neg-ℚ n)
        ( λ _ → refl-leq-ℚ zero-ℚ)
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

    leq-power-two-neg-sum-delta-finseq-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( power-two-neg-ℚ n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-finseq-adjoin-index-bounded-sequence-bool))
    leq-power-two-neg-sum-delta-finseq-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( delta-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-zero-delta-finseq-adjoin-index-bounded-sequence-bool)
          ( mod-succ-ℕ (k +ℕ n) n))
        ( leq-eq-ℚ
          ( inv
            ( eq-delta-finseq-selected-index-adjoin-index-bounded-sequence-bool)))

    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool :
      is-false (χ n) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( underlying-extended-finseq-bounded-sequence-bool i +ℚ
          delta-finseq-adjoin-index-bounded-sequence-bool i)
        ( summand-finseq-adjoin-index-bounded-sequence-bool
          ( i))
    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool-from-decidable :
      (χn=false : is-false (χ n)) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      (d : is-decidable (nat-Fin (k +ℕ succ-ℕ n) i ＝ n)) →
      leq-ℚ
        ( underlying-extended-finseq-bounded-sequence-bool i +ℚ
          delta-from-decidable-equality-index-adjoin-index-bounded-sequence-bool
            ( nat-Fin (k +ℕ succ-ℕ n) i)
            ( d))
        ( dyadic-summand-bool-ℚ
          ( nat-Fin (k +ℕ succ-ℕ n) i)
          ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i)))
    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool-from-decidable
      χn=false i (inl p) =
      transitive-leq-ℚ _ _ _
        ( leq-eq-ℚ
          ( inv
            ( ( ap
                ( dyadic-summand-bool-ℚ
                  ( nat-Fin (k +ℕ succ-ℕ n) i))
                ( eq-force-true-at-eq-sequence-bool χ n
                  ( nat-Fin (k +ℕ succ-ℕ n) i)
                  ( p))) ∙
              ( ap power-two-neg-ℚ p))))
        ( transitive-leq-ℚ _ _ _
          ( ind-bool
            ( λ b →
              is-false b →
              leq-ℚ
                ( (dyadic-summand-bool-ℚ n b) +ℚ
                  ( power-two-neg-ℚ n))
                ( power-two-neg-ℚ n))
            ( λ ())
            ( λ _ →
              leq-eq-ℚ
                ( left-unit-law-add-ℚ (power-two-neg-ℚ n)))
            ( χ n)
            ( χn=false))
          ( leq-eq-ℚ
            ( ap
              ( λ m →
                ( dyadic-summand-bool-ℚ m (χ m)) +ℚ
                ( power-two-neg-ℚ n))
              ( p))))
    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool-from-decidable
      χn=false i (inr q) =
      transitive-leq-ℚ _ _ _
        ( leq-eq-ℚ
          ( inv
            ( ap
              ( dyadic-summand-bool-ℚ (nat-Fin (k +ℕ succ-ℕ n) i))
              ( eq-force-true-at-neq-sequence-bool χ n
                ( nat-Fin (k +ℕ succ-ℕ n) i)
                ( q)))))
        ( transitive-leq-ℚ _ _ _
          ( leq-eq-ℚ
            ( right-unit-law-add-ℚ
              ( underlying-extended-finseq-bounded-sequence-bool i)))
          ( refl-leq-ℚ _))
    leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool
      χn=false i =
      leq-underlying-extended-add-delta-summand-finseq-adjoin-index-bounded-sequence-bool-from-decidable
        ( χn=false)
        ( i)
        ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  abstract
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-sum-adjoin-index-bounded-sequence-bool :
      is-false (χ n) →
      leq-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ
          power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-sum-adjoin-index-bounded-sequence-bool
      χn=false =
      transitive-leq-ℚ _ _ _
        ( preserves-leq-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( λ i →
            underlying-extended-finseq-bounded-sequence-bool i +ℚ
            delta-finseq-adjoin-index-bounded-sequence-bool
              ( i))
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
            ( leq-power-two-neg-sum-delta-finseq-adjoin-index-bounded-sequence-bool)))
```

## Dyadic sums of bounded boolean predicates with an adjoined index

The previous rational inequalities are now transported into $ℝₘ$ through the
canonical rational inclusion. Hence extending an index does not decrease the
corresponding family element. After monotone transport of admissibility from $x$
to $y$, we obtain the comparison between the underlying element at $x$ and the
extended element at $y$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-dyadic-sum-is-levy-admissible-bounded-sequence-bool :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x (S , adm-S))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
    leq-dyadic-sum-is-levy-admissible-bounded-sequence-bool
      n S x≤y adm-S y≰fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))
```

## A buound on the summands

$$
  2⁻ⁿ ≤ ∑_{j < k+n+1} χ'(j)2⁻ʲ.
$$

```agda
module _
  (n : ℕ) (S@(k , χ , _) : bounded-sequence-bool)
  where

  dyadic-summand-finseq-adjoin-index-bounded-sequence-bool :
    Fin (k +ℕ succ-ℕ n) → ℚ
  dyadic-summand-finseq-adjoin-index-bounded-sequence-bool i =
    dyadic-summand-bool-ℚ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  abstract
    compute-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool :
      dyadic-summand-finseq-adjoin-index-bounded-sequence-bool
        ( mod-succ-ℕ (k +ℕ n) n) ＝
      power-two-neg-ℚ n
    compute-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool =
      ap
        ( λ m → dyadic-summand-bool-ℚ m (force-true-at-sequence-bool χ n m))
        ( eq-nat-fin-mod-add-succ-ℕ k n) ∙
      ( ind-bool
        ( λ b →
          is-true b →
          dyadic-summand-bool-ℚ n b ＝
          power-two-neg-ℚ n)
        ( λ _ → refl)
        ( λ ())
        ( force-true-at-sequence-bool χ n n)
        ( is-true-force-true-at-self-sequence-bool χ n))

    leq-zero-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ zero-ℚ (dyadic-summand-finseq-adjoin-index-bounded-sequence-bool i)
    leq-zero-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool i =
      ind-bool
        ( λ b →
          leq-ℚ
            ( zero-ℚ)
            ( dyadic-summand-bool-ℚ (nat-Fin (k +ℕ succ-ℕ n) i) b))
        ( leq-zero-power-two-neg-ℚ (nat-Fin (k +ℕ succ-ℕ n) i))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-at-sequence-bool χ n (nat-Fin (k +ℕ succ-ℕ n) i))

  abstract
    leq-power-two-neg-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool :
      leq-ℚ
        ( power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-power-two-neg-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool =
      transitive-leq-ℚ _ _ _
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( dyadic-summand-finseq-adjoin-index-bounded-sequence-bool)
          ( leq-zero-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool)
          ( mod-succ-ℕ (k +ℕ n) n))
        ( leq-eq-ℚ
          ( inv
            ( compute-dyadic-summand-finseq-adjoin-index-bounded-sequence-bool)))
```

## For $f$-admissible $S$, if $y ≤ f(n)$ then $2⁻ⁿ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l)
  where

  abstract
    leq-power-two-neg-dyadic-sum-adjoin-index-is-levy-admissible-bounded-sequence-bool :
      (n : ℕ) (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f y S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-two-neg-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-bounded-sequence-bool f y
            ( S , adm-S)
            ( n)
            ( y≰fn)))
    leq-power-two-neg-dyadic-sum-adjoin-index-is-levy-admissible-bounded-sequence-bool
      n S adm-S y≰fn =
      leq-raise-macneille-real-ℚ
        ( power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-power-two-neg-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool n S)
```

## If $f(n) = x$, then $f$-admissibility at $x$ implies $n ∉ S$

```agda
abstract
  is-false-at-index-is-levy-admissible-bounded-sequence-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) (n : ℕ) →
    f n ＝ x →
    (S : bounded-sequence-bool) →
    is-levy-admissible-bounded-sequence-bool f x S →
    is-false (pr1 (pr2 S) n)
  is-false-at-index-is-levy-admissible-bounded-sequence-bool
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

## Dyadic sum estimate when adjoining disjoint indices

If $χ(n)$ is false we get

$$
  ∑_{i < k} χ(i)2⁻ⁱ + 2⁻ⁿ ≤ ∑_{j < k+n+1} χ'(j)2⁻ʲ.
$$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-adjoin-index-bounded-sequence-bool :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-adjoin-index-bounded-sequence-bool
      n fn=x x≤y S adm-S y≰fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ
          power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S)
          ( is-false-at-index-is-levy-admissible-bounded-sequence-bool
            ( f)
            ( x)
            ( n)
            ( fn=x)
            ( S)
            ( adm-S)))

    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-endomap-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : bounded-sequence-bool) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-endomap-levy-sequence-ℝₘ
      n fn=x x≤y S adm-S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ
            power-two-neg-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-adjoin-index-bounded-sequence-bool
          ( n)
          ( fn=x)
          ( x≤y)
          ( S)
          ( adm-S)
          ( y≰fn))

module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-dyadic-sum-is-levy-admissible-bounded-sequence-bool-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x (S , adm-S))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-dyadic-sum-is-levy-admissible-bounded-sequence-bool-endomap-levy-sequence-ℝₘ
      n S x≤y adm-S y≰fn =
      transitive-leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x (S , adm-S))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( leq-dyadic-sum-is-levy-admissible-bounded-sequence-bool
          ( f)
          ( x)
          ( y)
          ( n)
          ( S)
          ( x≤y)
          ( adm-S)
          ( y≰fn))

    leq-power-two-neg-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : bounded-sequence-bool) →
      (x≤y : leq-macneille-ℝ x y) →
      (adm-S : is-levy-admissible-bounded-sequence-bool f x S) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-two-neg-ℚ n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-power-two-neg-endomap-levy-sequence-ℝₘ
      n S x≤y adm-S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-two-neg-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-bounded-sequence-bool S n ,
            is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S
              ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
              ( y≰fn)))
        ( leq-power-two-neg-dyadic-sum-adjoin-index-is-levy-admissible-bounded-sequence-bool
          ( f)
          ( y)
          ( n)
          ( S)
          ( is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)
          ( y≰fn))
```

## Negative powers of two are positive

```agda
abstract
  le-zero-power-two-neg-ℚ :
    (n : ℕ) → le-ℚ zero-ℚ (power-two-neg-ℚ n)
  le-zero-power-two-neg-ℚ n =
    le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺)

  le-raise-zero-power-two-neg-ℚ :
    {l : Level} (n : ℕ) →
    le-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-real-ℚ l (power-two-neg-ℚ n))
  le-raise-zero-power-two-neg-ℚ {l} n =
    le-raise-macneille-real-ℚ
      ( zero-ℚ)
      ( power-two-neg-ℚ n)
      ( le-zero-power-two-neg-ℚ n)
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
    leq-two-endomap-levy-sequence-ℝₘ :
      (x : macneille-ℝ l) →
      leq-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f x)
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
    leq-two-endomap-levy-sequence-ℝₘ x =
      leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
        ( is-inhabited-levy-admissible-bounded-sequence-bool f x)
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
        ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x)

    is-postfixpoint-zero-endomap-levy-sequence-ℝₘ :
      is-postfixpoint-endomap-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f)
        ( raise-zero-macneille-ℝ l)
    is-postfixpoint-zero-endomap-levy-sequence-ℝₘ =
      is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-levy-admissible-bounded-sequence-bool f
          ( raise-zero-macneille-ℝ l))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f
          ( raise-zero-macneille-ℝ l))
        ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f
          ( raise-zero-macneille-ℝ l))
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f
          ( raise-zero-macneille-ℝ l))
        ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) ,
          ( λ _ ()))

  is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-ℝₘ :
    is-inhabited
      ( indexing-type-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f))
  is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-ℝₘ =
    unit-trunc-Prop
      ( raise-zero-macneille-ℝ l ,
        is-postfixpoint-zero-endomap-levy-sequence-ℝₘ)

  upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ : macneille-ℝ l
  upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ =
    raise-macneille-real-ℚ l (rational-ℕ 2)

  abstract
    is-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ :
      is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-postfixpoints-endomap-macneille-ℝ
          ( endomap-levy-sequence-ℝₘ f))
        ( upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ)
    is-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ (x , x≤gx) =
      transitive-leq-macneille-ℝ
        ( x)
        ( endomap-levy-sequence-ℝₘ f x)
        ( upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ)
        ( leq-two-endomap-levy-sequence-ℝₘ x)
        ( x≤gx)

  has-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ :
    Σ ( macneille-ℝ l)
      ( is-upper-bound-family-of-elements-macneille-ℝ
        ( family-of-elements-postfixpoints-endomap-macneille-ℝ
          ( endomap-levy-sequence-ℝₘ f)))
  has-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ =
    ( upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ ,
      is-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ)

  has-least-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ :
    has-least-upper-bound-family-of-elements-macneille-ℝ
      lzero
      ( family-of-elements-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f))
  has-least-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ =
    has-least-upper-bound-inhabited-upper-bounded-family-of-elements-macneille-ℝ
      ( is-inhabited-indexing-type-postfixpoints-endomap-levy-sequence-ℝₘ)
      ( family-of-elements-postfixpoints-endomap-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f))
      ( upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ)
      ( is-upper-bound-postfixpoints-endomap-levy-sequence-ℝₘ)
```

### The Levy point

We construct the _Levy point_ $x₀$ of a sequence of MacNeille reals $f : ℕ → ℝₘ$

$$
  x₀ ≔ sup\left\lbrace ∑_{i ∈ S}2⁻ⁱ \mvert S\text{ is finite self-}f\text{-admissible}\right\rbrace
$$

This is again well-defined by conditional order-completeness.

Notice that, instead of quantifying over all postfixpoints as with the
Knaster–Tarski fixed point theorem, we have specialized to dyadic sums of finite
self-$f$-admissible sets $S$, i.e., finite sets of natural numbers that are
$f$-admissible at their own dyadic sum.

The remaining argument shows $x₀ ∉ im(f)$.

```agda
is-levy-bounded-sequence-bool :
  {l : Level} → (ℕ → macneille-ℝ l) →
  bounded-sequence-bool → UU l
is-levy-bounded-sequence-bool {l} f S =
  is-levy-admissible-bounded-sequence-bool f
    ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
    ( S)

levy-bounded-sequence-bool :
  {l : Level} → (ℕ → macneille-ℝ l) → UU l
levy-bounded-sequence-bool f =
  Σ bounded-sequence-bool (is-levy-bounded-sequence-bool f)

dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  levy-bounded-sequence-bool f →
  macneille-ℝ l
dyadic-sum-levy-bounded-sequence-bool-ℝₘ {l} _ (S , _) =
  raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S

abstract
  is-inhabited-levy-bounded-sequence-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-inhabited (levy-bounded-sequence-bool f)
  is-inhabited-levy-bounded-sequence-bool
    _ =
    unit-trunc-Prop
      ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) , λ _ ())

upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
  {l : Level} (f : ℕ → macneille-ℝ l) → macneille-ℝ l
upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ {l} _ =
  raise-macneille-real-ℚ l (rational-ℕ 2)

abstract
  is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
  is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ
    f (S , _) =
    leq-raise-macneille-real-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool S)
      ( rational-ℕ 2)
      ( leq-two-dyadic-sum-ℚ-bounded-sequence-bool S)

has-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l)
    ( is-upper-bound-family-of-elements-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f))
has-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f =
  ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f ,
    is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)

point-levy-sequence-ℝₘ :
  {l : Level} → (ℕ → macneille-ℝ l) → macneille-ℝ l
point-levy-sequence-ℝₘ f =
  least-upper-bound-inhabited-bounded-family-macneille-ℝ
    ( is-inhabited-levy-bounded-sequence-bool f)
    ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
    ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
    ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)

abstract
  is-least-upper-bound-family-of-elements-point-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( point-levy-sequence-ℝₘ f)
  is-least-upper-bound-family-of-elements-point-levy-sequence-ℝₘ
    f =
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-bounded-sequence-bool f)
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)

  leq-family-element-point-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    (i : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f i)
      ( point-levy-sequence-ℝₘ f)
  leq-family-element-point-levy-sequence-ℝₘ f =
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-bounded-sequence-bool f)
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
```

### Contradiction at the Levy point

Assume $f(n) = x₀$. Then every self-$f$-admissible finite set $S$ avoids $n$, so
adjoining $n$ contributes $2⁻ⁿ$ to the dyadic sum. From this we derive that

$$
  x₀ + 2⁻ⁿ ≤ x₀,
$$

which is absurd since $2⁻ⁿ > 0$. Hence $f(n) ≠ x₀$ for all $n$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (let x0 = point-levy-sequence-ℝₘ f)
  where

  abstract
    leq-family-element-point-levy-sequence-ℝₘ' :
      ( S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      leq-macneille-ℝ (raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S) x0
    leq-family-element-point-levy-sequence-ℝₘ'
      S self-adm-S =
      leq-family-element-point-levy-sequence-ℝₘ f (S , self-adm-S)

    is-false-self-admissible-index-at-image-point-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      is-false (pr1 (pr2 S) n)
    is-false-self-admissible-index-at-image-point-levy-sequence-ℝₘ
      n fn=x0 S self-adm-S =
      is-false-at-index-is-levy-admissible-bounded-sequence-bool
        ( f)
        ( x0)
        ( n)
        ( fn=x0)
        ( S)
        ( is-levy-admissible-leq-bounded-sequence-bool f
          ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
          ( x0)
          ( leq-family-element-point-levy-sequence-ℝₘ' S self-adm-S)
          ( S)
          ( self-adm-S))

    leq-add-dyadic-sum-power-two-neg-sum-extend-self-admissible-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      leq-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
    leq-add-dyadic-sum-power-two-neg-sum-extend-self-admissible-levy-sequence-ℝₘ
      n fn=x0 S self-adm-S =
      leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-sum-adjoin-index-bounded-sequence-bool
        ( n)
        ( S)
        ( is-false-self-admissible-index-at-image-point-levy-sequence-ℝₘ
          ( n)
          ( fn=x0)
          ( S)
          ( self-adm-S))

    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-extend-self-admissible-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n))
        ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
    leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-extend-self-admissible-levy-sequence-ℝₘ
      n fn=x0 S self-adm-S =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-add-dyadic-sum-power-two-neg-sum-extend-self-admissible-levy-sequence-ℝₘ
          n fn=x0 S self-adm-S)

  abstract
    leq-dyadic-sum-bounded-sequence-bool-family-element-extend-self-admissible-levy-sequence-ℝₘ :
      (n : ℕ) →
      (S : bounded-sequence-bool) →
      leq-macneille-ℝ
        ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
        ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
    leq-dyadic-sum-bounded-sequence-bool-family-element-extend-self-admissible-levy-sequence-ℝₘ
      n S =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))

  abstract
    is-self-admissible-adjoin-not-leq-index-bounded-sequence-bool :
      (n : ℕ) →
      f n ＝ x0 →
      (S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      ¬ leq-macneille-ℝ
        ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
        ( x0) →
      is-levy-bounded-sequence-bool f
        ( adjoin-index-bounded-sequence-bool S n)
    is-self-admissible-adjoin-not-leq-index-bounded-sequence-bool
      n fn=x0 S self-adm-S extend-S≰x0 =
      is-levy-admissible-adjoin-index-bounded-sequence-bool
        ( f)
        ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
        ( n)
        ( S)
        ( λ m m∈S sum-extend-S≤fm →
          self-adm-S m m∈S
            ( transitive-leq-macneille-ℝ
              ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
              ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
              ( f m)
              ( sum-extend-S≤fm)
              ( leq-dyadic-sum-bounded-sequence-bool-family-element-extend-self-admissible-levy-sequence-ℝₘ
                ( n)
                ( S))))
        ( λ sum-extend-S≤fn →
          extend-S≰x0
            ( tr
              ( leq-macneille-ℝ
                ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n))
              ( fn=x0)
              ( sum-extend-S≤fn)))

    not-not-leq-family-element-extend-self-admissible-levy-sequence-ℝₘ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : bounded-sequence-bool) →
      is-levy-bounded-sequence-bool f S →
      ¬¬
        ( leq-macneille-ℝ
          ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
          ( x0))
    not-not-leq-family-element-extend-self-admissible-levy-sequence-ℝₘ
      n fn=x0 S self-adm-S extend-S≰x0 =
      extend-S≰x0
        ( leq-family-element-point-levy-sequence-ℝₘ f
          ( adjoin-index-bounded-sequence-bool S n ,
            is-self-admissible-adjoin-not-leq-index-bounded-sequence-bool
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S)
              ( extend-S≰x0)))

  abstract
    leq-right-translate-family-element-point-levy-sequence-ℝₘ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : bounded-sequence-bool) →
      ( self-adm-S :
        is-levy-bounded-sequence-bool f S) →
      leq-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( power-two-neg-ℚ n)
          ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
          ( S , self-adm-S))
        ( x0)
    leq-right-translate-family-element-point-levy-sequence-ℝₘ
      n fn=x0 S self-adm-S =
      let
        extend-S≤x0 :
          leq-macneille-ℝ
            ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
            ( x0)
        extend-S≤x0 =
          double-negation-elim-leq-left-raise-macneille-real-ℚ
            ( x0)
            ( dyadic-sum-ℚ-bounded-sequence-bool
              ( adjoin-index-bounded-sequence-bool S n))
            ( not-not-leq-family-element-extend-self-admissible-levy-sequence-ℝₘ
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S))

        add-sum-S+dyadic-coeff≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n))
            ( x0)
        add-sum-S+dyadic-coeff≤x0 =
          transitive-leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-two-neg-ℚ n))
            ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
            ( x0)
            ( extend-S≤x0)
            ( leq-add-dyadic-sum-bounded-sequence-bool-power-two-neg-family-element-extend-self-admissible-levy-sequence-ℝₘ
              ( n)
              ( fn=x0)
              ( S)
              ( self-adm-S))

        add-dyadic-coeff+sum-S≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( power-two-neg-ℚ n +ℚ dyadic-sum-ℚ-bounded-sequence-bool S))
            ( x0)
        add-dyadic-coeff+sum-S≤x0 =
          tr
            ( λ z → leq-macneille-ℝ z x0)
            ( ap
              ( raise-macneille-real-ℚ l)
              ( commutative-add-ℚ
                ( dyadic-sum-ℚ-bounded-sequence-bool S)
                ( power-two-neg-ℚ n)))
            ( add-sum-S+dyadic-coeff≤x0)
      in
        tr
          ( λ z → leq-macneille-ℝ z x0)
          ( inv
            ( eq-right-translate-raise-macneille-real-ℚ'
              ( power-two-neg-ℚ n)
              ( dyadic-sum-ℚ-bounded-sequence-bool S)))
          ( add-dyadic-coeff+sum-S≤x0)

    is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      is-upper-bound-family-of-elements-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( power-two-neg-ℚ n)
          ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f))
        ( x0)
    is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ
      n fn=x0 (S , self-adm-S) =
      leq-right-translate-family-element-point-levy-sequence-ℝₘ
        ( n)
        ( fn=x0)
        ( S)
        ( self-adm-S)

    leq-right-translate-point-levy-sequence-ℝₘ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      leq-macneille-ℝ
        ( add-macneille-ℝ
          ( located-macneille-real-ℚ (power-two-neg-ℚ n))
          ( x0))
        ( x0)
    leq-right-translate-point-levy-sequence-ℝₘ
      n fn=x0 =
      forward-implication
        ( is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
          ( power-two-neg-ℚ n)
          ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
          ( x0)
          ( is-least-upper-bound-family-of-elements-point-levy-sequence-ℝₘ f)
          ( x0))
        ( is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ n fn=x0)

    not-in-image-point-levy-sequence-ℝₘ :
      (n : ℕ) → f n ≠ x0
    not-in-image-point-levy-sequence-ℝₘ
      n fn=x0 =
      not-leq-right-translate-positive-macneille-real-ℚ
        ( x0)
        ( power-two-neg-ℚ n)
        ( le-zero-power-two-neg-ℚ n)
        ( leq-right-translate-point-levy-sequence-ℝₘ n fn=x0)
```

### Conclusion

We have produced a sequence-avoiding point for a general $f$: a point $x₀$
together with a proof that every index $n$ satisfies $f(n) ≠ x₀$.

```agda
sequence-avoiding-point-levy-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
sequence-avoiding-point-levy-macneille-ℝ f =
  ( point-levy-sequence-ℝₘ f ,
    not-in-image-point-levy-sequence-ℝₘ f)
```

## References

{{#bibliography}}
