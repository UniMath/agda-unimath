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
open import elementary-number-theory.dyadic-sums-bounded-boolean-predicates
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

## Formalization

### The dyadic sum of a bounded boolean predicate

Fix $f : ℕ → ℝₘ$ and $x : ℝₘ$. The type `bounded-sequence-bool` encodes bounded
boolean predicates `χ : ℕ → bool`

Hence admissible bounded boolean sequences represent finite sets of indices that
are extended to lie to the right of $x$ under $f$. Note, however, that they do
not form unique representations since the upper bound is not unique.

```agda
raise-dyadic-sum-ℝₘ-bounded-sequence-bool :
  (l : Level) → bounded-sequence-bool → macneille-ℝ l
raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S =
  raise-macneille-real-ℚ l (dyadic-sum-ℚ-bounded-sequence-bool S)
```

### Levy admissibility of boolean sequences and Levy's endomap

The results above establish that the family of dyadic sums over bounded boolean
sequences is inhabited and bounded, so using the conditional order-completeness
of the MacNeille reals we can define Levy’s endomap

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
  is-levy-admissible-bounded-sequence-bool S =
    (m : ℕ) →
    is-true (sequence-bool-bounded-sequence-bool S m) →
    ¬ leq-macneille-ℝ x (f m)

  levy-admissible-bounded-sequence-bool : UU l
  levy-admissible-bounded-sequence-bool =
    Σ (bounded-sequence-bool) (is-levy-admissible-bounded-sequence-bool)

  dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool :
    levy-admissible-bounded-sequence-bool →
    macneille-ℝ l
  dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool (S , _) =
    raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S

  is-levy-admissible-empty-bounded-sequence-bool :
    is-levy-admissible-bounded-sequence-bool (zero-ℕ , (λ ()))
  is-levy-admissible-empty-bounded-sequence-bool m m∈S =
    ex-falso
      ( is-not-true-is-false
        ( sequence-bool-bounded-sequence-bool (zero-ℕ , (λ ())) m)
        ( is-false-sequence-bool-bounded-sequence-bool-zero m)
        ( m∈S))

  point-levy-admissible-bounded-sequence-bool :
    levy-admissible-bounded-sequence-bool
  point-levy-admissible-bounded-sequence-bool =
    ( ( zero-ℕ , (λ ())) ,
      is-levy-admissible-empty-bounded-sequence-bool)

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

levy-admissible-leq-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  levy-admissible-bounded-sequence-bool f x →
  levy-admissible-bounded-sequence-bool f y
levy-admissible-leq-bounded-sequence-bool
  f x y x≤y (S , adm-S) =
  ( S , is-levy-admissible-leq-bounded-sequence-bool f x y x≤y S adm-S)

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
      ( λ S →
        is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( levy-admissible-leq-bounded-sequence-bool f x y x≤y S))
```

## Adjoining indices to boolean predicates on ℕ

Given an index $n$ and a boolean predicate $χ$ bounded by $k$, we can adjoin $n$
to $χ$ obtain a new bounded boolean predicate that is bounded at $k + n + 1$. We
could also have chosen the bound to be $\max\{k, n + 1\}$, but for the
formalization, we prefer the former as it avoids case splitting on whether
$n < k$.

If $χ$ and $\{n\}$ are admissible at $x$, then so is the extended predicate.

```agda
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
    ( is-true-adjoin-index-bounded-sequence-bool
      ( S)
      ( n)
      ( m)
      ( m∈extend-S))

adjoin-index-levy-admissible-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (S : levy-admissible-bounded-sequence-bool f y) (n : ℕ) →
  ¬ leq-macneille-ℝ y (f n) →
  levy-admissible-bounded-sequence-bool f y
adjoin-index-levy-admissible-bounded-sequence-bool f y (S , adm-S) n y≰fn =
  ( adjoin-index-bounded-sequence-bool S n ,
    is-levy-admissible-adjoin-index-bounded-sequence-bool f y n S adm-S y≰fn)

adjoin-index-levy-admissible-leq-bounded-sequence-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  (S : levy-admissible-bounded-sequence-bool f x) (n : ℕ) →
  ¬ leq-macneille-ℝ y (f n) →
  levy-admissible-bounded-sequence-bool f y
adjoin-index-levy-admissible-leq-bounded-sequence-bool
  f x y x≤y S =
  adjoin-index-levy-admissible-bounded-sequence-bool f y
    ( levy-admissible-leq-bounded-sequence-bool f x y x≤y S)
```

### Dyadic sums of bounded boolean predicates with an adjoined index

The previous rational inequalities are now transported into $ℝₘ$ through the
canonical rational inclusion. Hence extending an index does not decrease the
corresponding family element. After monotone transport of admissibility from $x$
to $y$, we obtain the comparison between the underlying element at $x$ and the
extended element at $y$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-dyadic-sum-levy-admissible-bounded-sequence-bool :
      (n : ℕ) →
      (S : levy-admissible-bounded-sequence-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x S)
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
    leq-dyadic-sum-levy-admissible-bounded-sequence-bool
      n (S , adm-S) y≰fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S))
```

### For $f$-admissible $S$, if $y ≤ f(n)$ then $2⁻ⁿ ≤ ∑_{i ∈ S ∪ \{n\}}2⁻ⁱ$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l)
  where

  abstract
    leq-power-one-half-dyadic-sum-adjoin-index-levy-admissible-bounded-sequence-bool :
      (n : ℕ) →
      (S : levy-admissible-bounded-sequence-bool f y) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-one-half-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-bounded-sequence-bool f y
            ( S)
            ( n)
            ( y≰fn)))
    leq-power-one-half-dyadic-sum-adjoin-index-levy-admissible-bounded-sequence-bool
      n (S , adm-S) y≰fn =
      leq-raise-macneille-real-ℚ
        ( power-one-half-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-power-one-half-levy-map-ℕ-sum-adjoin-index-bounded-sequence-bool n S)
```

### If $f(n) = x$, then $f$-admissibility at $x$ implies $n ∉ S$

```agda
abstract
  is-false-at-index-levy-admissible-bounded-sequence-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) (n : ℕ) →
    f n ＝ x →
    (S : levy-admissible-bounded-sequence-bool f x) →
    is-false (sequence-bool-bounded-sequence-bool (pr1 S) n)
  is-false-at-index-levy-admissible-bounded-sequence-bool
    f x n fn=x ((k , χ) , adm-S) =
    is-false-is-not-true
      ( sequence-bool-bounded-sequence-bool (k , χ) n)
      ( λ n∈S →
        adm-S n n∈S
          ( tr
            ( leq-macneille-ℝ x)
            ( inv fn=x)
            ( refl-leq-macneille-ℝ x)))
```

### Dyadic sum estimate when adjoining disjoint indices

If $χ(n)$ is false we get

$$
  ∑_{i < k} χ(i)2⁻ⁱ + 2⁻ⁿ ≤ ∑_{j < k+n+1} χ'(j)2⁻ʲ.
$$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (x y : macneille-ℝ l)
  (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-dyadic-sum+power-one-half-dyadic-sum-levy-admissible-bounded-sequence-bool-ℝₘ :
      (n : ℕ) →
      f n ＝ x →
      (S : levy-admissible-bounded-sequence-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool (pr1 S) +ℚ power-one-half-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
    leq-dyadic-sum+power-one-half-dyadic-sum-levy-admissible-bounded-sequence-bool-ℝₘ
      n fn=x (S , adm-S) y≰fn =
      leq-raise-macneille-real-ℚ
        ( dyadic-sum-ℚ-bounded-sequence-bool S +ℚ power-one-half-ℚ n)
        ( dyadic-sum-ℚ-bounded-sequence-bool
          ( adjoin-index-bounded-sequence-bool S n))
        ( leq-dyadic-sum+bool-power-one-half-sum-adjoin-index-bounded-sequence-bool
          ( n)
          ( S)
          ( is-false-at-index-levy-admissible-bounded-sequence-bool
            ( f)
            ( x)
            ( n)
            ( fn=x)
            ( S , adm-S)))

    leq-dyadic-sum+bool-power-one-half-endomap-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x →
      (S : levy-admissible-bounded-sequence-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool (pr1 S) +ℚ power-one-half-ℚ n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-dyadic-sum+bool-power-one-half-endomap-levy-sequence-ℝₘ
      n fn=x S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( dyadic-sum-ℚ-bounded-sequence-bool (pr1 S) +ℚ power-one-half-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( leq-dyadic-sum+power-one-half-dyadic-sum-levy-admissible-bounded-sequence-bool-ℝₘ
          ( n)
          ( fn=x)
          ( S)
          ( y≰fn))

module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-dyadic-sum-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : levy-admissible-bounded-sequence-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x S)
        ( endomap-levy-sequence-ℝₘ f y)
    leq-dyadic-sum-endomap-levy-sequence-ℝₘ
      n S y≰fn =
      transitive-leq-macneille-ℝ
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f x S)
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( leq-dyadic-sum-levy-admissible-bounded-sequence-bool f x y x≤y
          ( n)
          ( S)
          ( y≰fn))

    leq-power-one-half-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : levy-admissible-bounded-sequence-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-one-half-ℚ n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-power-one-half-endomap-levy-sequence-ℝₘ
      n S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-one-half-ℚ n))
        ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-bounded-sequence-bool f y)
          ( dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f y)
          ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool
            ( f)
            ( y))
          ( adjoin-index-levy-admissible-leq-bounded-sequence-bool f x y x≤y
            ( S)
            ( n)
            ( y≰fn)))
        ( leq-power-one-half-dyadic-sum-adjoin-index-levy-admissible-bounded-sequence-bool
          ( f)
          ( y)
          ( n)
          ( levy-admissible-leq-bounded-sequence-bool f x y x≤y S)
          ( y≰fn))
```

### Postfixpoints of the levy endomap

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
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f
          ( x))
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
        ( is-upper-bound-dyadic-sum-ℝₘ-levy-admissible-bounded-sequence-bool f
          ( x))

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
        ( ( zero-ℕ , ( λ ())) ,
          is-levy-admissible-empty-bounded-sequence-bool f
            ( raise-zero-macneille-ℝ l))

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
      ( lzero)
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

### The Levy fixpoint

We construct the _Levy fixpoint_ $x₀$ of a sequence of MacNeille reals
$f : ℕ → ℝₘ$

$$
  x₀ ≔ sup\left\lbrace ∑_{i ∈ S}2⁻ⁱ \mvert S\text{ is finite self-}f\text{-admissible}\right\rbrace
$$

This is again well-defined by conditional order-completeness.

Notice that, instead of quantifying over all postfixpoints as with the
Knaster–Tarski fixed point theorem, we have specialized to dyadic sums of finite
$f$-self-admissible sets $S$, i.e., finite sets of natural numbers that are
$f$-admissible at their own dyadic sum.

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
  is-inhabited-levy-bounded-sequence-bool {l} f =
    unit-trunc-Prop
      ( ( zero-ℕ , ( λ ())) ,
        is-levy-admissible-empty-bounded-sequence-bool f
          ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l (zero-ℕ , (λ ()))))

upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
  {l : Level} → (ℕ → macneille-ℝ l) → macneille-ℝ l
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

fixpoint-levy-sequence-ℝₘ :
  {l : Level} → (ℕ → macneille-ℝ l) → macneille-ℝ l
fixpoint-levy-sequence-ℝₘ f =
  least-upper-bound-inhabited-bounded-family-macneille-ℝ
    ( is-inhabited-levy-bounded-sequence-bool f)
    ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
    ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
    ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)

abstract
  is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( fixpoint-levy-sequence-ℝₘ f)
  is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ
    f =
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-bounded-sequence-bool f)
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)

  leq-dyadic-sum-fixpoint-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    (i : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f i)
      ( fixpoint-levy-sequence-ℝₘ f)
  leq-dyadic-sum-fixpoint-levy-sequence-ℝₘ f =
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-bounded-sequence-bool f)
      ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
      ( is-upper-bound-dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
```

### Contradiction at the Levy fixpoint

We argue that $x₀ ∉ \im(f)$.

Assume $f(n) = x₀$. Then every $f$-self-admissible finite set $S$ avoids $n$, so
adjoining $n$ contributes $2⁻ⁿ$ to the dyadic sum. From this we derive that

$$
  x₀ + 2⁻ⁿ ≤ x₀,
$$

which is absurd since $2⁻ⁿ > 0$. Hence $f(n) ≠ x₀$ for all $n$.

```agda
leq-dyadic-sum-adjoin-index-bounded-sequence-ℝₘ :
  {l : Level} (n : ℕ) →
  (S : bounded-sequence-bool) →
  leq-macneille-ℝ
    ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
    ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
leq-dyadic-sum-adjoin-index-bounded-sequence-ℝₘ
  n S =
  leq-raise-macneille-real-ℚ
    ( dyadic-sum-ℚ-bounded-sequence-bool S)
    ( dyadic-sum-ℚ-bounded-sequence-bool
      ( adjoin-index-bounded-sequence-bool S n))
    ( leq-dyadic-sum-bounded-sequence-bool-sum-adjoin-index-bounded-sequence-bool
      ( n)
      ( S))

module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (let x0 = fixpoint-levy-sequence-ℝₘ f)
  (n : ℕ) (fn=x0 : f n ＝ x0)
  where

  is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    is-false (sequence-bool-bounded-sequence-bool (pr1 S) n)
  is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ
    (S , self-adm-S) =
    is-false-at-index-levy-admissible-bounded-sequence-bool
      ( f)
      ( x0)
      ( n)
      ( fn=x0)
      ( levy-admissible-leq-bounded-sequence-bool f
        ( raise-dyadic-sum-ℝₘ-bounded-sequence-bool l S)
        ( x0)
        ( leq-dyadic-sum-fixpoint-levy-sequence-ℝₘ f (S , self-adm-S))
        ( S , self-adm-S))

  leq-add-dyadic-sum-power-one-half-sum-extend-self-admissible-levy-sequence-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    leq-ℚ
      ( dyadic-sum-ℚ-bounded-sequence-bool (pr1 S) +ℚ power-one-half-ℚ n)
      ( dyadic-sum-ℚ-bounded-sequence-bool
        ( adjoin-index-bounded-sequence-bool (pr1 S) n))
  leq-add-dyadic-sum-power-one-half-sum-extend-self-admissible-levy-sequence-ℝₘ
    (S , self-adm-S) =
    leq-dyadic-sum+bool-power-one-half-sum-adjoin-index-bounded-sequence-bool
      ( n)
      ( S)
      ( is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ
        ( S , self-adm-S))

  leq-dyadic-sum+bool-power-one-half-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-one-half-ℚ n +ℚ dyadic-sum-ℚ-bounded-sequence-bool (pr1 S)))
      ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l (pr1 S) n)
  leq-dyadic-sum+bool-power-one-half-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ
    (S , self-adm-S) =
    leq-raise-macneille-real-ℚ
      ( power-one-half-ℚ n +ℚ dyadic-sum-ℚ-bounded-sequence-bool S)
      ( dyadic-sum-ℚ-bounded-sequence-bool
        ( adjoin-index-bounded-sequence-bool S n))
      ( transitive-leq-ℚ _ _ _
        ( leq-add-dyadic-sum-power-one-half-sum-extend-self-admissible-levy-sequence-ℝₘ
          ( S , self-adm-S))
        ( leq-eq-ℚ
          ( inv
            ( commutative-add-ℚ
              ( dyadic-sum-ℚ-bounded-sequence-bool S)
              ( power-one-half-ℚ n)))))

  is-levy-adjoin-not-leq-index-bounded-sequence-bool :
    (S : bounded-sequence-bool) →
    is-levy-bounded-sequence-bool f S →
    ¬ leq-macneille-ℝ
      ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
      ( x0) →
    is-levy-bounded-sequence-bool f
      ( adjoin-index-bounded-sequence-bool S n)
  is-levy-adjoin-not-leq-index-bounded-sequence-bool
    S self-adm-S extend-S≰x0 =
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
            ( leq-dyadic-sum-adjoin-index-bounded-sequence-ℝₘ
              ( n)
              ( S))))
      ( λ sum-extend-S≤fn →
        extend-S≰x0
          ( tr
            ( leq-macneille-ℝ
              ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n))
            ( fn=x0)
            ( sum-extend-S≤fn)))

  not-not-leq-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    ¬¬
      ( leq-macneille-ℝ
        ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l (pr1 S) n)
        ( x0))
  not-not-leq-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ
    (S , self-adm-S) extend-S≰x0 =
    extend-S≰x0
      ( leq-dyadic-sum-fixpoint-levy-sequence-ℝₘ f
        ( adjoin-index-bounded-sequence-bool S n ,
          is-levy-adjoin-not-leq-index-bounded-sequence-bool
            ( S)
            ( self-adm-S)
            ( extend-S≰x0)))

  leq-dyadic-sum-adjoin-index-levy-bounded-sequence-bool-fixpoint-levy-sequence-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l (pr1 S) n)
      ( x0)
  leq-dyadic-sum-adjoin-index-levy-bounded-sequence-bool-fixpoint-levy-sequence-ℝₘ
    S =
    double-negation-elim-leq-left-raise-macneille-real-ℚ
      ( x0)
      ( dyadic-sum-ℚ-bounded-sequence-bool
        ( adjoin-index-bounded-sequence-bool (pr1 S) n))
      ( not-not-leq-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ S)

  is-upper-bound-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ' :
    (S : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-one-half-ℚ n +ℚ dyadic-sum-ℚ-bounded-sequence-bool (pr1 S)))
      ( x0)
  is-upper-bound-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ'
    ( S , self-adm-S) =
    transitive-leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-one-half-ℚ n +ℚ dyadic-sum-ℚ-bounded-sequence-bool S))
      ( raise-dyadic-sum-ℝₘ-adjoin-index-bounded-sequence-bool l S n)
      ( x0)
      ( leq-dyadic-sum-adjoin-index-levy-bounded-sequence-bool-fixpoint-levy-sequence-ℝₘ
        ( S , self-adm-S))
      ( leq-dyadic-sum+bool-power-one-half-dyadic-sum-adjoin-index-levy-bounded-sequence-ℝₘ
        ( S , self-adm-S))

  is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ :
    (S : levy-bounded-sequence-bool f) →
    leq-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ
        ( power-one-half-ℚ n)
        ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
        ( S))
      ( x0)
  is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ S =
    tr
      ( λ z → leq-macneille-ℝ z x0)
      ( inv
        ( eq-right-translate-raise-macneille-real-ℚ'
          ( power-one-half-ℚ n)
          ( dyadic-sum-ℚ-bounded-sequence-bool (pr1 S))))
      ( is-upper-bound-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ' S)

  leq-right-translate-fixpoint-levy-sequence-ℝₘ :
    leq-macneille-ℝ
      ( add-macneille-ℝ (located-macneille-real-ℚ (power-one-half-ℚ n)) x0)
      ( x0)
  leq-right-translate-fixpoint-levy-sequence-ℝₘ =
    forward-implication
      ( is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
        ( power-one-half-ℚ n)
        ( dyadic-sum-levy-bounded-sequence-bool-ℝₘ f)
        ( x0)
        ( is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ f)
        ( x0))
      ( is-upper-bound-right-translate-dyadic-sum-levy-bounded-sequence-bool-ℝₘ)
```

### Conclusion

We have produced a sequence-avoiding point for a general $f$: a point $x₀$
together with a proof that every index $n$ satisfies $f(n) ≠ x₀$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  where

  not-in-image-fixpoint-levy-sequence-ℝₘ :
    (n : ℕ) → f n ≠ fixpoint-levy-sequence-ℝₘ f
  not-in-image-fixpoint-levy-sequence-ℝₘ n fn=x0 =
    not-leq-right-translate-positive-macneille-real-ℚ
      ( fixpoint-levy-sequence-ℝₘ f)
      ( power-one-half-ℚ n)
      ( le-zero-power-one-half-ℚ n)
      ( leq-right-translate-fixpoint-levy-sequence-ℝₘ f n fn=x0)

  sequence-avoiding-point-levy-macneille-ℝ :
    Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
  sequence-avoiding-point-levy-macneille-ℝ =
    ( fixpoint-levy-sequence-ℝₘ f ,
      not-in-image-fixpoint-levy-sequence-ℝₘ)
```

## References

{{#bibliography}}
