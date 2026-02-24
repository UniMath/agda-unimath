# Levy's uncountability argument for MacNeille real numbers, predicatively

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import foundation.dependent-pair-types

module
  real-numbers.predicative-levy-uncountability-argument-macneille-real-numbers
  (r : ℚ) (0<r : le-ℚ zero-ℚ r) (r<1 : le-ℚ r one-ℚ)
  (let r⁺ = (r , is-positive-le-zero-ℚ 0<r))
  where
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
open import elementary-number-theory.geometric-sums-boolean-arrays
open import elementary-number-theory.inequalities-sums-of-finite-sequences-of-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
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
$i ∈ S$ implies that $x ≰ f(i)$. Essentially, this means elements of $S$ are
required to lie to the right of $x$ under $f$.

Fix some rational radius $0 < r < 1$, for example $r = ½$. We assign to each
subset $S$ the geometric sum $∑_{i ∈ S}rⁱ$. This defines a family of elements in
$ℝₘ$ which is inhabited (take $S$ the empty subset) and bounded above by
$1/(1-r)$, since

$$
  ∑_{i ∈ S}rⁱ ≤ ∑_{i ∈ ℕ}rⁱ = 1/(1-r).
$$

Hence by
[order completeness of the MacNeille reals](real-numbers.least-upper-bounds-families-macneille-real-numbers.md)
it has a least upper bound. This defines an endomap $g : ℝₘ → ℝₘ$,

$$
  g(x) ≔ \sup\left\lbrace ∑_{i ∈ S}rⁱ | S\text{ finite and admissible at }x \right\rbrace .
$$

Note that finite subsets can be encoded as arrays of booleans
$χ : \Fin k → bool$ so this construction is predicative.

Next, fix an index $n$ and adjoin it to $S$. This extension preserves finiteness
and yields the inequality $∑_{i ∈ S}rⁱ ≤ ∑_{i ∈ S ∪ \{n\}}rⁱ$. If $n ∉ S$, then
we may refine this inequality to:

$$
  ∑_{i ∈ S}rⁱ + rⁿ ≤ ∑_{i ∈ S ∪ \{n\}}rⁱ.
$$

Now restrict to _self-admissible_ finite subsets $S$, in the sense that $S$ is
admissible at its geometric sum $∑_{i ∈ S}rⁱ$. From the collection of
self-admissible finite subsets we may form an inhabited bounded family of
MacNeille reals. Let

$$
  x₀ ≔ \sup\left\lbrace ∑_{i ∈ S}rⁱ | S\text{ is self-admissible finite subset}\right\rbrace ,
$$

and assume for the sake of reaching a contradiction that $f(n) = x₀$. Then
$n ∉ S$ for any self-admissible finite subset $S$. Applying the extension
inequality and using the fact that $x₀$ is a least upper bound yields

$$
  x₀ + rⁿ ≤ x₀.
$$

Which is absurd. Therefore $f(n) ≠ x₀$ for all $n$. ∎

## Formalization

### The geometric sum over a boolean array

Fix $f : ℕ → ℝₘ$ and $x : ℝₘ$. The type `array-bool` encodes finite sequences of
booleans `χ : Fin k → bool`

Hence admissible boolean arrays represent finite sets of indices that are
extended to lie to the right of $x$ under $f$. Note, however, that they do not
form unique representations since the upper bound is not unique.

```agda
power-geometric-ratio-ℚ' : ℕ → ℚ
power-geometric-ratio-ℚ' = power-geometric-ratio-ℚ r⁺

le-zero-power-geometric-ratio-ℚ' :
  (n : ℕ) → le-ℚ zero-ℚ (power-geometric-ratio-ℚ' n)
le-zero-power-geometric-ratio-ℚ' = le-zero-power-geometric-ratio-ℚ r⁺

geometric-sum-ℚ-array-bool' :
  array-bool → ℚ
geometric-sum-ℚ-array-bool' =
  geometric-sum-ℚ-array-bool r⁺

adjoin-index-array-bool' :
  array-bool → ℕ → array-bool
adjoin-index-array-bool' = adjoin-index-array-bool r⁺

leq-bound-geometric-sum-ℚ-array-bool' :
  (S : array-bool) →
  leq-ℚ
    ( geometric-sum-ℚ-array-bool' S)
    ( geometric-series-bound-ℚ r r<1)
leq-bound-geometric-sum-ℚ-array-bool' =
  leq-bound-geometric-sum-ℚ-array-bool r⁺
    ( geometric-series-bound-ℚ r r<1)
    ( leq-zero-geometric-series-bound-ℚ r r<1)
    ( leq-one-plus-r-mul-geometric-series-bound-ℚ r r<1)

leq-geometric-sum-array-bool-sum-adjoin-index-array-bool' :
  (n : ℕ) (S : array-bool) →
  leq-ℚ
    ( geometric-sum-ℚ-array-bool' S)
    ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
leq-geometric-sum-array-bool-sum-adjoin-index-array-bool'
  n S =
  leq-geometric-sum-array-bool-sum-adjoin-index-array-bool
    r⁺ n S

leq-power-geometric-ratio-levy-map-ℕ-sum-adjoin-index-array-bool' :
  (n : ℕ) (S : array-bool) →
  leq-ℚ
    ( power-geometric-ratio-ℚ' n)
    ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
leq-power-geometric-ratio-levy-map-ℕ-sum-adjoin-index-array-bool'
  n S =
  leq-power-geometric-ratio-levy-map-ℕ-sum-adjoin-index-array-bool
    r⁺ n S

leq-geometric-sum+bool-power-geometric-ratio-sum-adjoin-index-array-bool' :
  (n : ℕ) (S : array-bool) →
  is-false (sequence-bool-array-bool S n) →
  leq-ℚ
    ( geometric-sum-ℚ-array-bool' S +ℚ power-geometric-ratio-ℚ' n)
    ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
leq-geometric-sum+bool-power-geometric-ratio-sum-adjoin-index-array-bool'
  n S =
  leq-geometric-sum+bool-power-geometric-ratio-sum-adjoin-index-array-bool
    r⁺ n S

is-true-adjoin-index-array-bool' :
  (S : array-bool) (n m : ℕ) →
  is-true (sequence-bool-array-bool (adjoin-index-array-bool' S n) m) →
  (m ＝ n) + is-true (sequence-bool-array-bool S m)
is-true-adjoin-index-array-bool' S n m =
  is-true-adjoin-index-array-bool r⁺ S n m

raise-geometric-sum-ℝₘ-array-bool :
  (l : Level) → array-bool → macneille-ℝ l
raise-geometric-sum-ℝₘ-array-bool l S =
  raise-macneille-real-ℚ l (geometric-sum-ℚ-array-bool' S)
```

### Levy admissibility of boolean arrays and Levy's endomap

The results above establish that the family of geometric sums over boolean
arrays is inhabited and bounded, so using the conditional order-completeness of
the MacNeille reals we can define Levy’s endomap

$$
  g(x) ≔ \sup\left\lbrace ∑_{i ∈ S}rⁱ | S\text{ finite and }$f$\text{-admissible at }x\right\rbrace ,
$$

where, as stated before, $S$ is $f$-admissible at $x$ if $m ∈ S$ implies
$x ≰ f(m)$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l)
  where

  is-levy-admissible-array-bool :
    array-bool → UU l
  is-levy-admissible-array-bool S =
    (m : ℕ) →
    is-true (sequence-bool-array-bool S m) →
    ¬ leq-macneille-ℝ x (f m)

  levy-admissible-array-bool : UU l
  levy-admissible-array-bool =
    Σ (array-bool) (is-levy-admissible-array-bool)

  geometric-sum-ℝₘ-levy-admissible-array-bool :
    levy-admissible-array-bool → macneille-ℝ l
  geometric-sum-ℝₘ-levy-admissible-array-bool (S , _) =
    raise-geometric-sum-ℝₘ-array-bool l S

  is-levy-admissible-empty-array-bool :
    is-levy-admissible-array-bool (zero-ℕ , ex-falso)
  is-levy-admissible-empty-array-bool m m∈S =
    ex-falso
      ( is-not-true-is-false
        ( sequence-bool-array-bool (zero-ℕ , ex-falso) m)
        ( is-false-sequence-bool-array-bool-zero m)
        ( m∈S))

  point-levy-admissible-array-bool :
    levy-admissible-array-bool
  point-levy-admissible-array-bool =
    ( (zero-ℕ , ex-falso) , is-levy-admissible-empty-array-bool)

  is-inhabited-levy-admissible-array-bool :
    is-inhabited levy-admissible-array-bool
  is-inhabited-levy-admissible-array-bool =
    unit-trunc-Prop point-levy-admissible-array-bool

  upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool :
    macneille-ℝ l
  upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool =
    raise-macneille-real-ℚ l (geometric-series-bound-ℚ r r<1)

  is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool :
    is-upper-bound-family-of-elements-macneille-ℝ
      ( geometric-sum-ℝₘ-levy-admissible-array-bool)
      ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)
  is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool
    ( S , _) =
    leq-raise-macneille-real-ℚ
      ( geometric-sum-ℚ-array-bool' S)
      ( geometric-series-bound-ℚ r r<1)
      ( leq-bound-geometric-sum-ℚ-array-bool' S)

  has-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool :
    Σ (macneille-ℝ l)
      ( is-upper-bound-family-of-elements-macneille-ℝ
        ( geometric-sum-ℝₘ-levy-admissible-array-bool))
  has-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool =
    ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool ,
      is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)
```

```agda
  endomap-levy-sequence-ℝₘ :
    macneille-ℝ l
  endomap-levy-sequence-ℝₘ =
    least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-admissible-array-bool)
      ( geometric-sum-ℝₘ-levy-admissible-array-bool)
      ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)
      ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)

  abstract
    is-least-upper-bound-geometric-sum-endomap-levy-sequence-ℝₘ :
      is-least-upper-bound-family-of-elements-macneille-ℝ
        ( geometric-sum-ℝₘ-levy-admissible-array-bool)
        ( endomap-levy-sequence-ℝₘ)
    is-least-upper-bound-geometric-sum-endomap-levy-sequence-ℝₘ =
      is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-levy-admissible-array-bool)
        ( geometric-sum-ℝₘ-levy-admissible-array-bool)
        ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)
        ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool)
```

```agda
is-levy-admissible-leq-array-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  (S : array-bool) →
  is-levy-admissible-array-bool f x S →
  is-levy-admissible-array-bool f y S
is-levy-admissible-leq-array-bool
  f x y x≤y S H m m∈S y≤fm =
  H m m∈S (transitive-leq-macneille-ℝ x y (f m) y≤fm x≤y)

levy-admissible-leq-array-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  levy-admissible-array-bool f x →
  levy-admissible-array-bool f y
levy-admissible-leq-array-bool
  f x y x≤y (S , adm-S) =
  (S , is-levy-admissible-leq-array-bool f x y x≤y S adm-S)

abstract
  is-increasing-endomap-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-increasing-endomap-macneille-ℝ (endomap-levy-sequence-ℝₘ f)
  is-increasing-endomap-levy-sequence-ℝₘ f x y x≤y =
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
      ( is-inhabited-levy-admissible-array-bool f x)
      ( geometric-sum-ℝₘ-levy-admissible-array-bool f x)
      ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f x)
      ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f x)
      ( endomap-levy-sequence-ℝₘ f y)
      ( λ S →
        is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-array-bool f y)
          ( geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( levy-admissible-leq-array-bool f x y x≤y S))
```

## Adjoining indices to boolean arrays

Given an index $n$ and a boolean boolean array $χ$ of length $k$, we can adjoin
$n$ to $χ$ obtain a new boolean array that of length $k + n + 1$. We could also
have chosen the bound to be $\max\{k, n + 1\}$, but for the formalization we
prefer the former as it avoids case splitting on whether $n < k$ or not.

If $χ$ and $\{n\}$ are admissible at $x$, then so is the extended array.

```agda
raise-geometric-sum-ℝₘ-adjoin-index-array-bool :
  (l : Level) → array-bool → ℕ → macneille-ℝ l
raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n =
  raise-geometric-sum-ℝₘ-array-bool l
    ( adjoin-index-array-bool' S n)

is-levy-admissible-adjoin-index-array-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (n : ℕ) (S : array-bool) →
  is-levy-admissible-array-bool f y S →
  ¬ leq-macneille-ℝ y (f n) →
  is-levy-admissible-array-bool f y
    ( adjoin-index-array-bool' S n)
is-levy-admissible-adjoin-index-array-bool
  f y n S adm-S y≰fn m m∈extend-S =
  rec-coproduct
    ( λ m=n → inv-tr (λ t → ¬ leq-macneille-ℝ y (f t)) m=n y≰fn)
    ( adm-S m)
    ( is-true-adjoin-index-array-bool' S n m m∈extend-S)

adjoin-index-levy-admissible-array-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (S : levy-admissible-array-bool f y) (n : ℕ) →
  ¬ leq-macneille-ℝ y (f n) →
  levy-admissible-array-bool f y
adjoin-index-levy-admissible-array-bool f y (S , adm-S) n y≰fn =
  ( adjoin-index-array-bool' S n ,
    is-levy-admissible-adjoin-index-array-bool f y n S adm-S y≰fn)

adjoin-index-levy-admissible-leq-array-bool :
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l) →
  leq-macneille-ℝ x y →
  (S : levy-admissible-array-bool f x) (n : ℕ) →
  ¬ leq-macneille-ℝ y (f n) →
  levy-admissible-array-bool f y
adjoin-index-levy-admissible-leq-array-bool
  f x y x≤y S =
  adjoin-index-levy-admissible-array-bool f y
    ( levy-admissible-leq-array-bool f x y x≤y S)
```

### Geometric sums over boolean arrays with an adjoined value

We transfer the previous inequalities to $ℝₘ$. Hence extending an index does not
decrease the corresponding geometric sum.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (x y : macneille-ℝ l) (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-geometric-sum-levy-admissible-array-bool :
      (n : ℕ) →
      (S : levy-admissible-array-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f x S)
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
    leq-geometric-sum-levy-admissible-array-bool
      n (S , adm-S) y≰fn =
      leq-raise-macneille-real-ℚ
        ( geometric-sum-ℚ-array-bool' S)
        ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
        ( leq-geometric-sum-array-bool-sum-adjoin-index-array-bool' n S)
```

### For $f$-admissible $S$, if $y ≤ f(n)$ then $rⁿ ≤ ∑_{i ∈ S ∪ \{n\}}rⁱ$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l)
  where

  abstract
    leq-power-geometric-ratio-geometric-sum-adjoin-index-levy-admissible-array-bool :
      (n : ℕ) →
      (S : levy-admissible-array-bool f y) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-geometric-ratio-ℚ' n))
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-array-bool f y S n y≰fn))
    leq-power-geometric-ratio-geometric-sum-adjoin-index-levy-admissible-array-bool
      n (S , adm-S) y≰fn =
      leq-raise-macneille-real-ℚ
        ( power-geometric-ratio-ℚ' n)
        ( geometric-sum-ℚ-array-bool'
          ( adjoin-index-array-bool' S n))
        ( leq-power-geometric-ratio-levy-map-ℕ-sum-adjoin-index-array-bool' n S)
```

### If $f(n) = x$, then $f$-admissibility at $x$ implies $n ∉ S$

```agda
abstract
  is-false-at-index-levy-admissible-array-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) (n : ℕ) →
    f n ＝ x →
    (S : levy-admissible-array-bool f x) →
    is-false (sequence-bool-array-bool (pr1 S) n)
  is-false-at-index-levy-admissible-array-bool
    f x n fn=x ((k , χ) , adm-S) =
    is-false-is-not-true
      ( sequence-bool-array-bool (k , χ) n)
      ( λ n∈S →
        adm-S n n∈S
          ( tr (leq-macneille-ℝ x) (inv fn=x) (refl-leq-macneille-ℝ x)))
```

### Geometric sum estimate when adjoining disjoint indices

If $χ(n)$ is false we get

$$
  (∑_{i < k} χ(i)rⁱ) + rⁿ ≤ ∑_{j < k+n+1} χ'(j)rʲ.
$$

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (x y : macneille-ℝ l)
  (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-geometric-sum+power-geometric-ratio-geometric-sum-levy-admissible-array-bool-ℝₘ :
      (n : ℕ) →
      f n ＝ x →
      (S : levy-admissible-array-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( geometric-sum-ℚ-array-bool' (pr1 S) +ℚ
            power-geometric-ratio-ℚ' n))
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
    leq-geometric-sum+power-geometric-ratio-geometric-sum-levy-admissible-array-bool-ℝₘ
      n fn=x (S , admS) y≰fn =
      leq-raise-macneille-real-ℚ
        ( geometric-sum-ℚ-array-bool' S +ℚ
          power-geometric-ratio-ℚ' n)
        ( geometric-sum-ℚ-array-bool'
          ( adjoin-index-array-bool' S n))
        ( leq-geometric-sum+bool-power-geometric-ratio-sum-adjoin-index-array-bool'
          ( n)
          ( S)
          ( is-false-at-index-levy-admissible-array-bool f x n fn=x (S , admS)))

    leq-geometric-sum+bool-power-geometric-ratio-endomap-levy-sequence-ℝₘ :
      (n : ℕ) →
      f n ＝ x →
      (S : levy-admissible-array-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( geometric-sum-ℚ-array-bool' (pr1 S) +ℚ power-geometric-ratio-ℚ' n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-geometric-sum+bool-power-geometric-ratio-endomap-levy-sequence-ℝₘ
      n fn=x S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( geometric-sum-ℚ-array-bool' (pr1 S) +ℚ
            power-geometric-ratio-ℚ' n))
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-array-bool f y)
          ( geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( leq-geometric-sum+power-geometric-ratio-geometric-sum-levy-admissible-array-bool-ℝₘ
          ( n)
          ( fn=x)
          ( S)
          ( y≰fn))

module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  (x≤y : leq-macneille-ℝ x y)
  where

  abstract
    leq-geometric-sum-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : levy-admissible-array-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f x S)
        ( endomap-levy-sequence-ℝₘ f y)
    leq-geometric-sum-endomap-levy-sequence-ℝₘ
      n S y≰fn =
      transitive-leq-macneille-ℝ
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f x S)
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-array-bool f y)
          ( geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( leq-geometric-sum-levy-admissible-array-bool f x y x≤y n S y≰fn)

    leq-power-geometric-ratio-endomap-levy-sequence-ℝₘ :
      (n : ℕ) (S : levy-admissible-array-bool f x) →
      (y≰fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-geometric-ratio-ℚ' n))
        ( endomap-levy-sequence-ℝₘ f y)
    leq-power-geometric-ratio-endomap-levy-sequence-ℝₘ
      n S y≰fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l (power-geometric-ratio-ℚ' n))
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f y
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( endomap-levy-sequence-ℝₘ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-levy-admissible-array-bool f y)
          ( geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f y)
          ( adjoin-index-levy-admissible-leq-array-bool f x y x≤y S n y≰fn))
        ( leq-power-geometric-ratio-geometric-sum-adjoin-index-levy-admissible-array-bool
          ( f)
          ( y)
          ( n)
          ( levy-admissible-leq-array-bool f x y x≤y S)
          ( y≰fn))
```

### Postfixpoints of the Levy endomap

From the estimates above, $g(x) ≤ \frac{1}{1-r}$ for all $x$, and $0$ is a
postfixpoint.

Therefore the family of postfixpoints is inhabited and bounded above, so it has
a least upper bound, which is a greatest postfixpoint for $g$.

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  where

  abstract
    leq-two-endomap-levy-sequence-ℝₘ :
      (x : macneille-ℝ l) →
      leq-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f x)
        ( raise-macneille-real-ℚ l (geometric-series-bound-ℚ r r<1))
    leq-two-endomap-levy-sequence-ℝₘ x =
      leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
        ( is-inhabited-levy-admissible-array-bool f x)
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f x)
        ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f x)
        ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f x)
        ( raise-macneille-real-ℚ l (geometric-series-bound-ℚ r r<1))
        ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f x)

    is-postfixpoint-zero-endomap-levy-sequence-ℝₘ :
      is-postfixpoint-endomap-macneille-ℝ
        ( endomap-levy-sequence-ℝₘ f)
        ( raise-zero-macneille-ℝ l)
    is-postfixpoint-zero-endomap-levy-sequence-ℝₘ =
      is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-levy-admissible-array-bool f
          ( raise-zero-macneille-ℝ l))
        ( geometric-sum-ℝₘ-levy-admissible-array-bool f
          ( raise-zero-macneille-ℝ l))
        ( upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f
          ( raise-zero-macneille-ℝ l))
        ( is-upper-bound-geometric-sum-ℝₘ-levy-admissible-array-bool f
          ( raise-zero-macneille-ℝ l))
        ( ( zero-ℕ , ex-falso) ,
          is-levy-admissible-empty-array-bool f (raise-zero-macneille-ℝ l))

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
    raise-macneille-real-ℚ l (geometric-series-bound-ℚ r r<1)

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
    has-least-upper-bound-family-of-elements-macneille-ℝ lzero
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
$f : ℕ → ℝₘ$,

$$
  x₀ ≔ sup\left\lbrace ∑_{i ∈ S}rⁱ \mvert S\text{ is finite self-}f\text{-admissible}\right\rbrace .
$$

This is again well-defined by conditional order-completeness.

Notice that, instead of quantifying over all postfixpoints as with the
Knaster–Tarski fixed point theorem, we have specialized to geometric sums of
finite $f$-self-admissible sets $S$, i.e., finite sets of natural numbers that
are $f$-admissible at their own geometric sum.

```agda
is-levy-self-admissible-array-bool :
  {l : Level} → (ℕ → macneille-ℝ l) →
  array-bool → UU l
is-levy-self-admissible-array-bool {l} f S =
  is-levy-admissible-array-bool f
    ( raise-geometric-sum-ℝₘ-array-bool l S)
    ( S)

levy-self-admissible-array-bool :
  {l : Level} → (ℕ → macneille-ℝ l) → UU l
levy-self-admissible-array-bool f =
  Σ array-bool (is-levy-self-admissible-array-bool f)

geometric-sum-levy-self-admissible-array-bool-ℝₘ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  levy-self-admissible-array-bool f →
  macneille-ℝ l
geometric-sum-levy-self-admissible-array-bool-ℝₘ {l} _ (S , _) =
  raise-geometric-sum-ℝₘ-array-bool l S

abstract
  is-inhabited-levy-self-admissible-array-bool :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-inhabited (levy-self-admissible-array-bool f)
  is-inhabited-levy-self-admissible-array-bool {l} f =
    unit-trunc-Prop
      ( ( zero-ℕ , ex-falso) ,
        is-levy-admissible-empty-array-bool f
          ( raise-geometric-sum-ℝₘ-array-bool l (zero-ℕ , ex-falso)))

upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ :
  {l : Level} → (ℕ → macneille-ℝ l) → macneille-ℝ l
upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ {l} _ =
  raise-macneille-real-ℚ l (geometric-series-bound-ℚ r r<1)

abstract
  is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-upper-bound-family-of-elements-macneille-ℝ
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
  is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ
    f (S , _) =
    leq-raise-macneille-real-ℚ
      ( geometric-sum-ℚ-array-bool' S)
      ( geometric-series-bound-ℚ r r<1)
      ( leq-bound-geometric-sum-ℚ-array-bool' S)

has-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l)
    ( is-upper-bound-family-of-elements-macneille-ℝ
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f))
has-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f =
  ( upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f ,
    is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)

fixpoint-levy-sequence-ℝₘ :
  {l : Level} → (ℕ → macneille-ℝ l) → macneille-ℝ l
fixpoint-levy-sequence-ℝₘ f =
  least-upper-bound-inhabited-bounded-family-macneille-ℝ
    ( is-inhabited-levy-self-admissible-array-bool f)
    ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
    ( upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
    ( is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)

abstract
  is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-macneille-ℝ
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( fixpoint-levy-sequence-ℝₘ f)
  is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ f =
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-self-admissible-array-bool f)
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)

  leq-geometric-sum-fixpoint-levy-sequence-ℝₘ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    (i : levy-self-admissible-array-bool f) →
    leq-macneille-ℝ
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f i)
      ( fixpoint-levy-sequence-ℝₘ f)
  leq-geometric-sum-fixpoint-levy-sequence-ℝₘ f =
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-levy-self-admissible-array-bool f)
      ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
      ( is-upper-bound-geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
```

### Contradiction at the Levy fixpoint

We argue that $x₀ ∉ \im(f)$.

Assume $f(n) = x₀$. Then every $f$-self-admissible finite set $S$ avoids $n$, so
adjoining $n$ contributes $rⁿ$ to the geometric sum. From this we derive that

$$
  x₀ + rⁿ ≤ x₀,
$$

which is absurd since $rⁿ > 0$. Hence $f(n) ≠ x₀$ for all $n$.

```agda
leq-geometric-sum-adjoin-index-bounded-sequence-ℝₘ :
  {l : Level} (n : ℕ) →
  (S : array-bool) →
  leq-macneille-ℝ
    ( raise-geometric-sum-ℝₘ-array-bool l S)
    ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n)
leq-geometric-sum-adjoin-index-bounded-sequence-ℝₘ n S =
  leq-raise-macneille-real-ℚ
    ( geometric-sum-ℚ-array-bool' S)
    ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
    ( leq-geometric-sum-array-bool-sum-adjoin-index-array-bool' n S)

module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (let x0 = fixpoint-levy-sequence-ℝₘ f)
  (n : ℕ) (fn=x0 : f n ＝ x0)
  where

  is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    is-false (sequence-bool-array-bool (pr1 S) n)
  is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ
    (S , self-adm-S) =
    is-false-at-index-levy-admissible-array-bool
      ( f)
      ( x0)
      ( n)
      ( fn=x0)
      ( levy-admissible-leq-array-bool f
        ( raise-geometric-sum-ℝₘ-array-bool l S)
        ( x0)
        ( leq-geometric-sum-fixpoint-levy-sequence-ℝₘ f (S , self-adm-S))
        ( S , self-adm-S))

  leq-add-geometric-sum-power-geometric-ratio-sum-extend-self-admissible-levy-sequence-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    leq-ℚ
      ( geometric-sum-ℚ-array-bool' (pr1 S) +ℚ power-geometric-ratio-ℚ' n)
      ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' (pr1 S) n))
  leq-add-geometric-sum-power-geometric-ratio-sum-extend-self-admissible-levy-sequence-ℝₘ
    (S , self-adm-S) =
    leq-geometric-sum+bool-power-geometric-ratio-sum-adjoin-index-array-bool'
      ( n)
      ( S)
      ( is-false-self-admissible-index-at-image-fixpoint-levy-sequence-ℝₘ
        ( S , self-adm-S))

  leq-geometric-sum+bool-power-geometric-ratio-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-geometric-ratio-ℚ' n +ℚ geometric-sum-ℚ-array-bool' (pr1 S)))
      ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l (pr1 S) n)
  leq-geometric-sum+bool-power-geometric-ratio-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ
    (S , self-adm-S) =
    leq-raise-macneille-real-ℚ
      ( power-geometric-ratio-ℚ' n +ℚ geometric-sum-ℚ-array-bool' S)
      ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' S n))
      ( transitive-leq-ℚ _ _ _
        ( leq-add-geometric-sum-power-geometric-ratio-sum-extend-self-admissible-levy-sequence-ℝₘ
          ( S , self-adm-S))
        ( leq-eq-ℚ
          ( inv
            ( commutative-add-ℚ
              ( geometric-sum-ℚ-array-bool' S)
              ( power-geometric-ratio-ℚ' n)))))

  is-levy-self-admissible-adjoin-not-leq-index-array-bool :
    (S : array-bool) →
    is-levy-self-admissible-array-bool f S →
    ¬ leq-macneille-ℝ
      ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n)
      ( x0) →
    is-levy-self-admissible-array-bool f (adjoin-index-array-bool' S n)
  is-levy-self-admissible-adjoin-not-leq-index-array-bool
    S self-adm-S extend-S≰x0 =
    is-levy-admissible-adjoin-index-array-bool
      ( f)
      ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n)
      ( n)
      ( S)
      ( λ m m∈S sum-extend-S≤fm →
        self-adm-S m m∈S
          ( transitive-leq-macneille-ℝ
            ( raise-geometric-sum-ℝₘ-array-bool l S)
            ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n)
            ( f m)
            ( sum-extend-S≤fm)
            ( leq-geometric-sum-adjoin-index-bounded-sequence-ℝₘ n S)))
      ( λ sum-extend-S≤fn →
        extend-S≰x0
          ( tr
            ( leq-macneille-ℝ
              ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n))
            ( fn=x0)
            ( sum-extend-S≤fn)))

  not-not-leq-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    ¬¬
      ( leq-macneille-ℝ
        ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l (pr1 S) n)
        ( x0))
  not-not-leq-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ
    (S , self-adm-S) extend-S≰x0 =
    extend-S≰x0
      ( leq-geometric-sum-fixpoint-levy-sequence-ℝₘ f
        ( adjoin-index-array-bool' S n ,
          is-levy-self-admissible-adjoin-not-leq-index-array-bool
            ( S)
            ( self-adm-S)
            ( extend-S≰x0)))

  leq-geometric-sum-adjoin-index-levy-self-admissible-array-bool-fixpoint-levy-sequence-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    leq-macneille-ℝ
      ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l (pr1 S) n)
      ( x0)
  leq-geometric-sum-adjoin-index-levy-self-admissible-array-bool-fixpoint-levy-sequence-ℝₘ
    S =
    double-negation-elim-leq-left-raise-macneille-real-ℚ
      ( x0)
      ( geometric-sum-ℚ-array-bool' (adjoin-index-array-bool' (pr1 S) n))
      ( not-not-leq-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ S)

  is-upper-bound-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ' :
    (S : levy-self-admissible-array-bool f) →
    leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-geometric-ratio-ℚ' n +ℚ geometric-sum-ℚ-array-bool' (pr1 S)))
      ( x0)
  is-upper-bound-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ'
    ( S , self-adm-S) =
    transitive-leq-macneille-ℝ
      ( raise-macneille-real-ℚ l
        ( power-geometric-ratio-ℚ' n +ℚ geometric-sum-ℚ-array-bool' S))
      ( raise-geometric-sum-ℝₘ-adjoin-index-array-bool l S n)
      ( x0)
      ( leq-geometric-sum-adjoin-index-levy-self-admissible-array-bool-fixpoint-levy-sequence-ℝₘ
        ( S , self-adm-S))
      ( leq-geometric-sum+bool-power-geometric-ratio-geometric-sum-adjoin-index-levy-bounded-sequence-ℝₘ
        ( S , self-adm-S))

  is-upper-bound-right-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ :
    (S : levy-self-admissible-array-bool f) →
    leq-macneille-ℝ
      ( translate-family-right-macneille-real-ℚ
        ( power-geometric-ratio-ℚ' n)
        ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
        ( S))
      ( x0)
  is-upper-bound-right-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ
    S =
    tr
      ( λ z → leq-macneille-ℝ z x0)
      ( inv
        ( eq-right-translate-raise-macneille-real-ℚ'
          ( power-geometric-ratio-ℚ' n)
          ( geometric-sum-ℚ-array-bool' (pr1 S))))
      ( is-upper-bound-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ'
        ( S))

  leq-right-translate-fixpoint-levy-sequence-ℝₘ :
    leq-macneille-ℝ
      ( add-macneille-ℝ
        ( located-macneille-real-ℚ (power-geometric-ratio-ℚ' n))
        ( x0))
      ( x0)
  leq-right-translate-fixpoint-levy-sequence-ℝₘ =
    forward-implication
      ( is-least-upper-bound-family-of-elements-at-level-right-translate-macneille-real-ℚ
        ( power-geometric-ratio-ℚ' n)
        ( geometric-sum-levy-self-admissible-array-bool-ℝₘ f)
        ( x0)
        ( is-least-upper-bound-family-of-elements-fixpoint-levy-sequence-ℝₘ f)
        ( x0))
      ( is-upper-bound-right-translate-geometric-sum-levy-self-admissible-array-bool-ℝₘ)
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
      ( power-geometric-ratio-ℚ' n)
      ( le-zero-power-geometric-ratio-ℚ' n)
      ( leq-right-translate-fixpoint-levy-sequence-ℝₘ f n fn=x0)

  sequence-avoiding-point-levy-macneille-ℝ :
    Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
  sequence-avoiding-point-levy-macneille-ℝ =
    ( fixpoint-levy-sequence-ℝₘ f ,
      not-in-image-fixpoint-levy-sequence-ℝₘ)
```

## References

{{#bibliography}}
