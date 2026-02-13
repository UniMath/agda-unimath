# Levy's uncountability argument for MacNeille real numbers, predicatively and constructively

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
open import foundation.double-negation
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
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
open import real-numbers.least-upper-bounds-translation-addition-macneille-real-numbers
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

## Levy family and endomap

```agda
levy-base-index-sequence-macneille-ℝ : UU lzero
levy-base-index-sequence-macneille-ℝ =
  Σ ℕ (λ k → Σ (ℕ → bool) (λ χ → (m : ℕ) → leq-ℕ k m → is-false (χ m)))

is-admissible-levy-base-index-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  levy-base-index-sequence-macneille-ℝ → UU l
is-admissible-levy-base-index-sequence-macneille-ℝ f x (k , χ , _) =
  (m : ℕ) → is-true (χ m) → ¬ leq-macneille-ℝ x (f m)

indexing-type-levy-family-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) → UU l
indexing-type-levy-family-sequence-macneille-ℝ f x =
  Σ levy-base-index-sequence-macneille-ℝ
    (is-admissible-levy-base-index-sequence-macneille-ℝ f x)

weight-levy-sequence-macneille-ℝ : ℕ → ℚ
weight-levy-sequence-macneille-ℝ n =
  power-ℚ n one-half-ℚ

selected-weight-levy-sequence-macneille-ℝ : ℕ → bool → ℚ
selected-weight-levy-sequence-macneille-ℝ n =
  rec-bool
    ( weight-levy-sequence-macneille-ℝ n)
    ( zero-ℚ)

sum-levy-base-index-sequence-macneille-ℝ :
  levy-base-index-sequence-macneille-ℝ → ℚ
sum-levy-base-index-sequence-macneille-ℝ (k , χ , _) =
  sum-fin-sequence-ℚ k
    ( λ i →
      selected-weight-levy-sequence-macneille-ℝ
        ( nat-Fin k i)
        ( χ (nat-Fin k i)))

family-of-elements-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  indexing-type-levy-family-sequence-macneille-ℝ f x →
  macneille-ℝ l
family-of-elements-levy-sequence-macneille-ℝ {l} _ _ (S , _) =
  raise-macneille-real-ℚ l (sum-levy-base-index-sequence-macneille-ℝ S)

is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  is-inhabited (indexing-type-levy-family-sequence-macneille-ℝ f x)
is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ _ _ =
  unit-trunc-Prop
    ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) ,
      λ _ ())

abstract
  leq-zero-weight-levy-sequence-macneille-ℝ :
    (n : ℕ) →
    leq-ℚ zero-ℚ (weight-levy-sequence-macneille-ℝ n)
  leq-zero-weight-levy-sequence-macneille-ℝ n =
    leq-le-ℚ
      ( le-zero-is-positive-ℚ
        ( is-positive-power-ℚ⁺ n one-half-ℚ⁺))

  leq-selected-weight-levy-sequence-macneille-ℝ :
    (n : ℕ) (b : bool) →
    leq-ℚ
      ( selected-weight-levy-sequence-macneille-ℝ n b)
      ( weight-levy-sequence-macneille-ℝ n)
  leq-selected-weight-levy-sequence-macneille-ℝ n true =
    refl-leq-ℚ (weight-levy-sequence-macneille-ℝ n)
  leq-selected-weight-levy-sequence-macneille-ℝ n false =
    leq-zero-weight-levy-sequence-macneille-ℝ n

  leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ :
    (S : levy-base-index-sequence-macneille-ℝ) →
    leq-ℚ
      ( sum-levy-base-index-sequence-macneille-ℝ S)
      ( sum-fin-sequence-ℚ
        ( pr1 S)
        ( λ i →
          weight-levy-sequence-macneille-ℝ
            ( nat-Fin (pr1 S) i)))
  leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ (k , χ , _) =
    preserves-leq-sum-fin-sequence-ℚ
      ( k)
      ( λ i →
        selected-weight-levy-sequence-macneille-ℝ
          ( nat-Fin k i)
          ( χ (nat-Fin k i)))
      ( λ i →
        weight-levy-sequence-macneille-ℝ (nat-Fin k i))
      ( λ i →
        leq-selected-weight-levy-sequence-macneille-ℝ
          ( nat-Fin k i)
          ( χ (nat-Fin k i)))

  eq-sum-all-weights-sum-standard-geometric-one-half-ℚ :
    (k : ℕ) →
    sum-fin-sequence-ℚ
      k
      ( λ i →
        weight-levy-sequence-macneille-ℝ (nat-Fin k i)) ＝
    sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k
  eq-sum-all-weights-sum-standard-geometric-one-half-ℚ k =
    ap
      ( sum-fin-sequence-ℚ k)
      ( eq-htpy
        ( λ i →
          inv
            ( compute-standard-geometric-sequence-ℚ
              one-ℚ
              one-half-ℚ
              ( nat-Fin k i) ∙
              left-unit-law-mul-ℚ
                ( power-ℚ (nat-Fin k i) one-half-ℚ))))

  leq-two-sum-all-weights-levy-base-index-sequence-macneille-ℝ :
    (k : ℕ) →
    leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        ( λ i →
          weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
      ( rational-ℕ 2)
  leq-two-sum-all-weights-levy-base-index-sequence-macneille-ℝ k =
    transitive-leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        ( λ i →
          weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
      ( sum-standard-geometric-fin-sequence-ℚ one-ℚ one-half-ℚ k)
      ( rational-ℕ 2)
      ( leq-rational-two-sum-standard-geometric-one-half-ℚ k)
      ( leq-eq-ℚ
        ( eq-sum-all-weights-sum-standard-geometric-one-half-ℚ k))

  leq-two-sum-levy-base-index-sequence-macneille-ℝ :
    (S : levy-base-index-sequence-macneille-ℝ) →
    leq-ℚ
      ( sum-levy-base-index-sequence-macneille-ℝ S)
      ( rational-ℕ 2)
  leq-two-sum-levy-base-index-sequence-macneille-ℝ (k , χ , χ-outside-k) =
    transitive-leq-ℚ
      ( sum-levy-base-index-sequence-macneille-ℝ (k , χ , χ-outside-k))
      ( sum-fin-sequence-ℚ
        k
        ( λ i →
          weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
      ( rational-ℕ 2)
      ( leq-two-sum-all-weights-levy-base-index-sequence-macneille-ℝ k)
      ( leq-sum-levy-base-index-map-ℕ-sum-all-weights-macneille-ℝ
        ( k , χ , χ-outside-k))

upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  macneille-ℝ l
upper-bound-family-of-elements-levy-sequence-macneille-ℝ {l} _ _ =
  raise-macneille-real-ℚ l (rational-ℕ 2)

is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  is-upper-bound-family-of-elements-macneille-ℝ
    ( family-of-elements-levy-sequence-macneille-ℝ f x)
    ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)
is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ _ _ (S , _) =
  leq-raise-macneille-real-ℚ
    ( sum-levy-base-index-sequence-macneille-ℝ S)
    ( rational-ℕ 2)
    ( leq-two-sum-levy-base-index-sequence-macneille-ℝ S)

has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
  Σ (macneille-ℝ l)
    ( is-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-levy-sequence-macneille-ℝ f x))
has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x =
  ( upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x ,
    is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)

endomap-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  macneille-ℝ l → macneille-ℝ l
endomap-levy-sequence-macneille-ℝ f x =
  least-upper-bound-inhabited-bounded-family-macneille-ℝ
    ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f x)
    ( family-of-elements-levy-sequence-macneille-ℝ f x)
    ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
    ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))

abstract
  is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( endomap-levy-sequence-macneille-ℝ f x)
  is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ f x =
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f x)
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
      ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))

abstract
  is-least-upper-bound-family-of-elements-at-level-endomap-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-at-level-macneille-ℝ
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( endomap-levy-sequence-macneille-ℝ f x)
  is-least-upper-bound-family-of-elements-at-level-endomap-levy-sequence-macneille-ℝ
    f x =
    is-least-upper-bound-family-of-elements-at-level-is-least-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( endomap-levy-sequence-macneille-ℝ f x)
      ( is-least-upper-bound-family-of-elements-endomap-levy-sequence-macneille-ℝ
        f x)

is-admissible-leq-levy-base-index-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) {x y : macneille-ℝ l} →
  leq-macneille-ℝ x y →
  (S : levy-base-index-sequence-macneille-ℝ) →
  is-admissible-levy-base-index-sequence-macneille-ℝ f x S →
  is-admissible-levy-base-index-sequence-macneille-ℝ f y S
is-admissible-leq-levy-base-index-sequence-macneille-ℝ
  f {x} {y} x≤y S H m m∈S =
  λ y≤fm →
    H m m∈S
      ( transitive-leq-macneille-ℝ
        x
        y
        ( f m)
        ( y≤fm)
        ( x≤y))

abstract
  is-increasing-endomap-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-increasing-endomap-macneille-ℝ
      ( endomap-levy-sequence-macneille-ℝ f)
  is-increasing-endomap-levy-sequence-macneille-ℝ f x y x≤y =
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ
      ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f x)
      ( family-of-elements-levy-sequence-macneille-ℝ f x)
      ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
      ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
      ( endomap-levy-sequence-macneille-ℝ f y)
      ( λ where
        (S , admissible-S-x) →
          is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
            ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
            ( family-of-elements-levy-sequence-macneille-ℝ f y)
            ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
            ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
            ( S ,
              is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S-x))
```

## Forcing a single index

```agda
force-true-from-decidable-equality-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
  is-decidable (m ＝ n) →
  bool
force-true-from-decidable-equality-ℕ n χ m (inl _) = true
force-true-from-decidable-equality-ℕ n χ m (inr _) = χ m

eq-force-true-from-decidable-equality-inl-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) (p : m ＝ n) →
  force-true-from-decidable-equality-ℕ n χ m (inl p) ＝ true
eq-force-true-from-decidable-equality-inl-ℕ n χ m p = refl

eq-force-true-from-decidable-equality-inr-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) (p : m ＝ n → empty) →
  force-true-from-decidable-equality-ℕ n χ m (inr p) ＝ χ m
eq-force-true-from-decidable-equality-inr-ℕ n χ m p = refl

force-true-ℕ :
  ℕ → (ℕ → bool) → ℕ → bool
force-true-ℕ n χ m =
  force-true-from-decidable-equality-ℕ
    n
    χ
    m
    ( has-decidable-equality-ℕ m n)

is-true-force-true-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
  is-true (force-true-ℕ n χ m) →
  (m ＝ n) + is-true (χ m)
is-true-force-true-ℕ n χ m =
  ind-coproduct
    ( λ d →
      is-true (force-true-from-decidable-equality-ℕ n χ m d) →
      (m ＝ n) + is-true (χ m))
    ( λ p _ → inl p)
    ( λ _ H' → inr H')
    ( has-decidable-equality-ℕ m n)

is-false-force-true-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
  m ≠ n →
  is-false (χ m) →
  is-false (force-true-ℕ n χ m)
is-false-force-true-ℕ n χ m =
  ind-coproduct
    ( λ d →
      m ≠ n →
      is-false (χ m) →
      is-false (force-true-from-decidable-equality-ℕ n χ m d))
    ( λ p neq' _ → ex-falso (neq' p))
    ( λ _ _ χm=false' → χm=false')
    ( has-decidable-equality-ℕ m n)

is-true-force-true-self-ℕ :
  (n : ℕ) (χ : ℕ → bool) →
  is-true (force-true-ℕ n χ n)
is-true-force-true-self-ℕ n χ =
  ind-coproduct
    ( λ d → is-true (force-true-from-decidable-equality-ℕ n χ n d))
    ( λ _ → refl)
    ( λ n≠n → ex-falso (n≠n refl))
    ( has-decidable-equality-ℕ n n)

eq-force-true-neq-ℕ :
  (n : ℕ) (χ : ℕ → bool) (m : ℕ) →
  m ≠ n → force-true-ℕ n χ m ＝ χ m
eq-force-true-neq-ℕ n χ m =
  ind-coproduct
    ( λ d → m ≠ n → force-true-from-decidable-equality-ℕ n χ m d ＝ χ m)
    ( λ p m≠n' → ex-falso (m≠n' p))
    ( λ _ _ → refl)
    ( has-decidable-equality-ℕ m n)

extend-levy-base-index-force-true-sequence-macneille-ℝ :
  ℕ →
  levy-base-index-sequence-macneille-ℝ →
  levy-base-index-sequence-macneille-ℝ
extend-levy-base-index-force-true-sequence-macneille-ℝ
  n (k , (χ , χ-outside-k)) =
  ( k +ℕ succ-ℕ n ,
    force-true-ℕ n χ ,
    λ m n+k≤m →
      is-false-force-true-ℕ n χ m
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
        ( χ-outside-k
          ( m)
          ( transitive-leq-ℕ k (k +ℕ succ-ℕ n) m
            ( n+k≤m)
            ( leq-add-ℕ k (succ-ℕ n)))))

is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l) →
  (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ) →
  ( (m : ℕ) → is-true (pr1 (pr2 S) m) → ¬ leq-macneille-ℝ y (f m)) →
  ¬ leq-macneille-ℝ y (f n) →
  is-admissible-levy-base-index-sequence-macneille-ℝ f y
    ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)
is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
  f y n S admissible-S not-y≤fn m m∈extend-S =
  rec-coproduct
    ( λ m=n →
      tr
        ( λ t → ¬ leq-macneille-ℝ y (f t))
        ( inv m=n)
        ( not-y≤fn))
    ( λ m∈S → admissible-S m m∈S)
    ( is-true-force-true-ℕ n (pr1 (pr2 S)) m m∈extend-S)
```

## Sum estimates for forced indices

```agda
module _
  (n : ℕ) (S@(k , χ , _) : levy-base-index-sequence-macneille-ℝ)
  (let extended-S = extend-levy-base-index-force-true-sequence-macneille-ℝ n S)
  where

  old-fin-sequence-levy-base-index-sequence-macneille-ℝ : Fin k → ℚ
  old-fin-sequence-levy-base-index-sequence-macneille-ℝ i =
    selected-weight-levy-sequence-macneille-ℝ (nat-Fin k i) (χ (nat-Fin k i))

  inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
    Fin k → ℚ
  inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ i =
    selected-weight-levy-sequence-macneille-ℝ
      ( nat-Fin k i)
      ( force-true-ℕ n χ (nat-Fin k i))

  extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
    Fin (k +ℕ succ-ℕ n) → ℚ
  extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i =
    selected-weight-levy-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( force-true-ℕ n χ (nat-Fin (k +ℕ succ-ℕ n) i))

  inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
    Fin (succ-ℕ n) → ℚ
  inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ =
    extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
    inr-coproduct-Fin k (succ-ℕ n)

  abstract
    eq-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin k) →
      inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
        ( i) ＝
      extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
        ( inl-coproduct-Fin k (succ-ℕ n) i)
    eq-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
      i =
      ap
        ( λ m →
          selected-weight-levy-sequence-macneille-ℝ m (force-true-ℕ n χ m))
        ( inv (nat-inl-coproduct-Fin k (succ-ℕ n) i))

    leq-old-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin k) →
      leq-ℚ
        ( old-fin-sequence-levy-base-index-sequence-macneille-ℝ i)
        ( inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
          ( i))
    leq-old-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
      i =
      ind-coproduct
        ( λ d →
          leq-ℚ
            ( old-fin-sequence-levy-base-index-sequence-macneille-ℝ i)
            ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin k i)
              ( force-true-from-decidable-equality-ℕ n χ (nat-Fin k i) d)))
        ( λ _ →
          ind-bool
            ( λ b →
              leq-ℚ
                ( selected-weight-levy-sequence-macneille-ℝ
                  ( nat-Fin k i)
                  b)
                ( weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
            ( refl-leq-ℚ (weight-levy-sequence-macneille-ℝ (nat-Fin k i)))
            ( leq-zero-weight-levy-sequence-macneille-ℝ (nat-Fin k i))
            ( χ (nat-Fin k i)))
        ( λ _ →
          refl-leq-ℚ
            ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin k i)
              ( χ (nat-Fin k i))))
        ( has-decidable-equality-ℕ (nat-Fin k i) n)

    leq-zero-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        zero-ℚ
        ( inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
          i)
    leq-zero-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            zero-ℚ
            ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                ( inr-coproduct-Fin
                  k
                  ( succ-ℕ n)
                  i))
              b))
        ( leq-zero-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            ( inr-coproduct-Fin
              k
              ( succ-ℕ n)
              i)))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-ℕ
          n
          χ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            ( inr-coproduct-Fin
              k
              ( succ-ℕ n)
              i)))

    leq-zero-sum-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
      leq-ℚ
        zero-ℚ
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
    leq-zero-sum-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ =
      transitive-leq-ℚ
        zero-ℚ
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( λ _ → zero-ℚ))
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
        ( preserves-leq-sum-fin-sequence-ℚ
          ( succ-ℕ n)
          ( λ _ → zero-ℚ)
          ( inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
          ( leq-zero-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ))
        ( leq-eq-ℚ
          ( inv
            ( eq-sum-zero-fin-sequence-ℚ
              ( succ-ℕ n))))

    eq-sum-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ :
      sum-fin-sequence-ℚ
        k
        inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ ＝
      sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n))
    eq-sum-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( eq-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ))

  leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-force-true-sequence-macneille-ℝ :
    leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        old-fin-sequence-levy-base-index-sequence-macneille-ℝ)
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)))
  leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-force-true-sequence-macneille-ℝ =
    transitive-leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        old-fin-sequence-levy-base-index-sequence-macneille-ℝ)
      ( sum-fin-sequence-ℚ
        k
        inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)))
      ( leq-eq-ℚ
        eq-sum-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
      ( preserves-leq-sum-fin-sequence-ℚ
        k
        old-fin-sequence-levy-base-index-sequence-macneille-ℝ
        inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ
        leq-old-inl-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)

  leq-sum-inl-extended-fin-sequence-sum-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
    leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)))
      ( sum-fin-sequence-ℚ
        ( k +ℕ succ-ℕ n)
        extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
  leq-sum-inl-extended-fin-sequence-sum-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ =
    transitive-leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)))
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)) +ℚ
        sum-fin-sequence-ℚ
          ( succ-ℕ n)
          inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
      ( sum-fin-sequence-ℚ
        ( k +ℕ succ-ℕ n)
        extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
      ( leq-eq-ℚ
        ( inv
          ( split-sum-fin-sequence-ℚ
            k
            ( succ-ℕ n)
            extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)))
      ( transitive-leq-ℚ
        ( sum-fin-sequence-ℚ
          k
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
            inl-coproduct-Fin
              k
              ( succ-ℕ n)))
        ( sum-fin-sequence-ℚ
          k
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
            inl-coproduct-Fin
              k
              ( succ-ℕ n)) +ℚ
          zero-ℚ)
        ( sum-fin-sequence-ℚ
          k
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
            inl-coproduct-Fin
              k
              ( succ-ℕ n)) +ℚ
          sum-fin-sequence-ℚ
            ( succ-ℕ n)
            inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
        ( preserves-leq-right-add-ℚ
          ( sum-fin-sequence-ℚ
            k
            ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
              inl-coproduct-Fin
                k
                ( succ-ℕ n)))
          zero-ℚ
          ( sum-fin-sequence-ℚ
            ( succ-ℕ n)
            inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
          leq-zero-sum-inr-fin-sequence-extended-levy-base-index-force-true-sequence-macneille-ℝ)
        ( leq-eq-ℚ
          ( inv
            ( right-unit-law-add-ℚ
              ( sum-fin-sequence-ℚ
                k
                ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
                  inl-coproduct-Fin
                    k
                    ( succ-ℕ n)))))))

  leq-sum-levy-base-index-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ :
    leq-ℚ
      ( sum-levy-base-index-sequence-macneille-ℝ S)
      ( sum-levy-base-index-sequence-macneille-ℝ extended-S)
  leq-sum-levy-base-index-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ =
    transitive-leq-ℚ
      ( sum-fin-sequence-ℚ
        k
        old-fin-sequence-levy-base-index-sequence-macneille-ℝ)
      ( sum-fin-sequence-ℚ
        k
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ ∘
          inl-coproduct-Fin
            k
            ( succ-ℕ n)))
      ( sum-fin-sequence-ℚ
        ( k +ℕ succ-ℕ n)
        extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
      leq-sum-inl-extended-fin-sequence-sum-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
      leq-sum-old-fin-sequence-sum-inl-extended-levy-base-index-force-true-sequence-macneille-ℝ

  old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
    Fin (k +ℕ succ-ℕ n) → ℚ
  old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i =
    selected-weight-levy-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( χ (nat-Fin (k +ℕ succ-ℕ n) i))

  inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
    Fin k → ℚ
  inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ =
    old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ ∘
    inl-coproduct-Fin
      k
      ( succ-ℕ n)

  inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
    Fin (succ-ℕ n) → ℚ
  inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ =
    old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ ∘
    inr-coproduct-Fin
      k
      ( succ-ℕ n)

  delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ :
    (m : ℕ) → is-decidable (m ＝ n) → ℚ
  delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ m (inl _) =
    weight-levy-sequence-macneille-ℝ n
  delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ m (inr _) =
    zero-ℚ

  delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
    Fin (k +ℕ succ-ℕ n) → ℚ
  delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i =
    delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
      ( nat-Fin (k +ℕ succ-ℕ n) i)
      ( has-decidable-equality-ℕ (nat-Fin (k +ℕ succ-ℕ n) i) n)

  i-n : Fin (k +ℕ succ-ℕ n)
  i-n = mod-succ-ℕ (k +ℕ n) n

  abstract
    eq-nat-Fin-i-n :
      nat-Fin (k +ℕ succ-ℕ n) i-n ＝ n
    eq-nat-Fin-i-n =
      eq-cong-le-ℕ
        ( k +ℕ succ-ℕ n)
        ( nat-Fin (k +ℕ succ-ℕ n) i-n)
        ( n)
        ( strict-upper-bound-nat-Fin
          ( k +ℕ succ-ℕ n)
          ( i-n))
        ( concatenate-le-leq-ℕ
          { x = n}
          { y = succ-ℕ n}
          { z = k +ℕ succ-ℕ n}
          ( succ-le-ℕ n)
          ( leq-add-ℕ' (succ-ℕ n) k))
        ( cong-nat-mod-succ-ℕ
          ( k +ℕ n)
          ( n))

    eq-old-fin-sequence-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
      (i : Fin k) →
      old-fin-sequence-levy-base-index-sequence-macneille-ℝ i ＝
      inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i
    eq-old-fin-sequence-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
      i =
      ap
        ( λ m →
          selected-weight-levy-sequence-macneille-ℝ m (χ m))
        ( inv
          ( nat-inl-coproduct-Fin
            k
            ( succ-ℕ n)
            i))

    leq-zero-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
      (i : Fin (succ-ℕ n)) →
      leq-ℚ
        zero-ℚ
        ( inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i)
    leq-zero-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            zero-ℚ
            ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                ( inr-coproduct-Fin
                  k
                  ( succ-ℕ n)
                  i))
              b))
        ( leq-zero-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            ( inr-coproduct-Fin
              k
              ( succ-ℕ n)
              i)))
        ( refl-leq-ℚ zero-ℚ)
        ( χ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            ( inr-coproduct-Fin
              k
              ( succ-ℕ n)
              i)))

    eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
      sum-fin-sequence-ℚ
        k
        old-fin-sequence-levy-base-index-sequence-macneille-ℝ ＝
      sum-fin-sequence-ℚ
        k
        inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
    eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ =
      ap
        ( sum-fin-sequence-ℚ k)
        ( eq-htpy
          ( eq-old-fin-sequence-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ))

    leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
      leq-ℚ
        ( sum-fin-sequence-ℚ
          k
          old-fin-sequence-levy-base-index-sequence-macneille-ℝ)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
    leq-zero-sum-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ :
      leq-ℚ
        zero-ℚ
        ( sum-fin-sequence-ℚ
          ( succ-ℕ n)
          inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
    leq-zero-sum-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ =
      leq-zero-sum-fin-sequence-ℚ
        ( succ-ℕ n)
        inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
        leq-zero-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ

    leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ =
      transitive-leq-ℚ
        ( sum-fin-sequence-ℚ
          k
          old-fin-sequence-levy-base-index-sequence-macneille-ℝ)
        ( sum-fin-sequence-ℚ
          k
          inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
        ( transitive-leq-ℚ
          ( sum-fin-sequence-ℚ
            k
            inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
          ( sum-fin-sequence-ℚ
            k
            inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ +ℚ
            sum-fin-sequence-ℚ
              ( succ-ℕ n)
              inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
          ( sum-fin-sequence-ℚ
            ( k +ℕ succ-ℕ n)
            old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
          ( leq-eq-ℚ
            ( inv
              ( split-sum-fin-sequence-ℚ
                k
                ( succ-ℕ n)
                old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)))
          ( transitive-leq-ℚ
            ( sum-fin-sequence-ℚ
              k
              inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
            ( sum-fin-sequence-ℚ
              k
              inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ +ℚ
              zero-ℚ)
            ( sum-fin-sequence-ℚ
              k
              inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ +ℚ
              sum-fin-sequence-ℚ
                ( succ-ℕ n)
                inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
            ( preserves-leq-right-add-ℚ
              ( sum-fin-sequence-ℚ
                k
                inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
              zero-ℚ
              ( sum-fin-sequence-ℚ
                ( succ-ℕ n)
                inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
              leq-zero-sum-inr-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)
            ( leq-eq-ℚ
              ( inv
                ( right-unit-law-add-ℚ
                  ( sum-fin-sequence-ℚ
                    k
                    inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ))))))
        ( leq-eq-ℚ
          eq-sum-old-fin-sequence-sum-inl-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ)

    eq-delta-fin-sequence-selected-index-levy-base-index-force-true-sequence-macneille-ℝ :
      delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i-n ＝
      weight-levy-sequence-macneille-ℝ n
    eq-delta-fin-sequence-index-eq-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
      delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i ＝
      weight-levy-sequence-macneille-ℝ n
    eq-delta-fin-sequence-index-eq-levy-base-index-force-true-sequence-macneille-ℝ
      i
      p =
      ind-coproduct
        ( λ d →
          nat-Fin (k +ℕ succ-ℕ n) i ＝ n →
          delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            d ＝
          weight-levy-sequence-macneille-ℝ n)
        ( λ _ _ → refl)
        ( λ q p' → ex-falso (q p'))
        ( has-decidable-equality-ℕ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          n)
        p

    eq-delta-fin-sequence-index-neq-zero-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      (nat-Fin (k +ℕ succ-ℕ n) i ＝ n → empty) →
      delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i ＝ zero-ℚ
    eq-delta-fin-sequence-index-neq-zero-levy-base-index-force-true-sequence-macneille-ℝ
      i
      q =
      ind-coproduct
        ( λ d →
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i ＝ n → empty) →
          delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            d ＝
          zero-ℚ)
        ( λ p q' → ex-falso (q' p))
        ( λ _ _ → refl)
        ( has-decidable-equality-ℕ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          n)
        q

    eq-delta-fin-sequence-selected-index-levy-base-index-force-true-sequence-macneille-ℝ
      =
      eq-delta-fin-sequence-index-eq-levy-base-index-force-true-sequence-macneille-ℝ
        i-n
        eq-nat-Fin-i-n

    eq-old-extended-fin-sequence-index-levy-base-index-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i ＝
      selected-weight-levy-sequence-macneille-ℝ
        ( nat-Fin (k +ℕ succ-ℕ n) i)
        ( χ (nat-Fin (k +ℕ succ-ℕ n) i))
    eq-old-extended-fin-sequence-index-levy-base-index-sequence-macneille-ℝ i =
      refl

    leq-zero-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        zero-ℚ
        ( delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i)
    leq-zero-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i
      =
      ind-coproduct
        ( λ d →
          leq-ℚ
            zero-ℚ
            ( delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                i)
              d))
        ( λ _ → leq-zero-weight-levy-sequence-macneille-ℝ n)
        ( λ _ → refl-leq-ℚ zero-ℚ)
        ( has-decidable-equality-ℕ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          n)

    leq-weight-sum-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
      leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
    leq-weight-sum-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ =
      transitive-leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i-n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
        ( leq-term-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
          leq-zero-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
          i-n)
        ( leq-eq-ℚ
          ( inv
            ( eq-delta-fin-sequence-selected-index-levy-base-index-force-true-sequence-macneille-ℝ)))

    leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ :
      is-false (χ n) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      leq-ℚ
        ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
          delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i)
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ i)
    leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-from-decidable :
      (χn=false : is-false (χ n)) →
      (i : Fin (k +ℕ succ-ℕ n)) →
      (d : is-decidable (nat-Fin (k +ℕ succ-ℕ n) i ＝ n)) →
      leq-ℚ
        ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
          delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            d)
        ( selected-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          ( force-true-from-decidable-equality-ℕ
            n
            χ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            d))
    leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-from-decidable
      χn=false
      i
      ( inl p) =
      transitive-leq-ℚ
        ( ( selected-weight-levy-sequence-macneille-ℝ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            ( χ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                i))) +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( weight-levy-sequence-macneille-ℝ n)
        ( selected-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          ( force-true-from-decidable-equality-ℕ
            n
            χ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            ( inl p)))
        ( leq-eq-ℚ
          ( ap
              weight-levy-sequence-macneille-ℝ
              ( inv p) ∙
            inv
              ( ap
                ( λ b →
                  selected-weight-levy-sequence-macneille-ℝ
                    ( nat-Fin
                      ( k +ℕ succ-ℕ n)
                      i)
                    b)
                ( eq-force-true-from-decidable-equality-inl-ℕ
                  n
                  χ
                  ( nat-Fin
                    ( k +ℕ succ-ℕ n)
                    i)
                  p))))
        ( transitive-leq-ℚ
          ( ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                i)
              ( χ
                ( nat-Fin
                  ( k +ℕ succ-ℕ n)
                  i))) +ℚ
            weight-levy-sequence-macneille-ℝ n)
          ( ( selected-weight-levy-sequence-macneille-ℝ n (χ n)) +ℚ
            weight-levy-sequence-macneille-ℝ n)
          ( weight-levy-sequence-macneille-ℝ n)
          ( ind-bool
            ( λ b →
              is-false b →
              leq-ℚ
                ( (selected-weight-levy-sequence-macneille-ℝ n b) +ℚ
                  weight-levy-sequence-macneille-ℝ n)
                ( weight-levy-sequence-macneille-ℝ n))
            ( λ ())
            ( λ _ →
              leq-eq-ℚ
                ( left-unit-law-add-ℚ
                  ( weight-levy-sequence-macneille-ℝ n)))
            ( χ n)
            ( χn=false))
          ( leq-eq-ℚ
            ( ap
              ( λ m →
                ( selected-weight-levy-sequence-macneille-ℝ m (χ m)) +ℚ
                weight-levy-sequence-macneille-ℝ n)
              ( p))))
    leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-from-decidable
      χn=false
      i
      ( inr q) =
      transitive-leq-ℚ
        ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
          delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            ( inr q))
        ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i)
        ( selected-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          ( force-true-from-decidable-equality-ℕ
            n
            χ
            ( nat-Fin
              ( k +ℕ succ-ℕ n)
              i)
            ( inr q)))
        ( leq-eq-ℚ
          ( inv
            ( ap
              ( λ b →
                selected-weight-levy-sequence-macneille-ℝ
                  ( nat-Fin
                    ( k +ℕ succ-ℕ n)
                    i)
                  b)
              ( eq-force-true-from-decidable-equality-inr-ℕ
                n
                χ
                ( nat-Fin
                  ( k +ℕ succ-ℕ n)
                  i)
                q))))
        ( transitive-leq-ℚ
          ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
            delta-from-decidable-equality-index-levy-base-index-force-true-sequence-macneille-ℝ
              ( nat-Fin
                ( k +ℕ succ-ℕ n)
                i)
              ( inr q))
          ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
            zero-ℚ)
          ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i)
          ( leq-eq-ℚ
            ( right-unit-law-add-ℚ
              ( old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
                i)))
          ( leq-eq-ℚ refl))
    leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
      χn=false i =
      leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-from-decidable
        χn=false
        i
        ( has-decidable-equality-ℕ
          ( nat-Fin
            ( k +ℕ succ-ℕ n)
            i)
          n)

  abstract
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ :
      is-false (χ n) →
      leq-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ extended-S)
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
      χn=false =
      transitive-leq-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( λ i →
            old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
            delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
              i))
        ( sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
        ( preserves-leq-sum-fin-sequence-ℚ
          ( k +ℕ succ-ℕ n)
          ( λ i →
            old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
            delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
              i)
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
          ( leq-old-extended-add-delta-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
            χn=false))
        ( transitive-leq-ℚ
          ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
            weight-levy-sequence-macneille-ℝ n)
          ( sum-fin-sequence-ℚ
            ( k +ℕ succ-ℕ n)
            old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ +ℚ
            sum-fin-sequence-ℚ
              ( k +ℕ succ-ℕ n)
              delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ)
          ( sum-fin-sequence-ℚ
            ( k +ℕ succ-ℕ n)
            ( λ i →
              old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ i +ℚ
              delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ
                i))
          ( leq-eq-ℚ
            ( interchange-add-sum-fin-sequence-ℚ
              ( k +ℕ succ-ℕ n)
              old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
              delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ))
          ( preserves-leq-add-ℚ
            leq-sum-old-fin-sequence-sum-old-extended-fin-sequence-levy-base-index-sequence-macneille-ℝ
            leq-weight-sum-delta-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ))
```

## Forced family elements

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ :
      (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ) →
      (x≤y : leq-macneille-ℝ x y) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          x
          ( S ,
            admissible-S))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
      n S x≤y admissible-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ
            n
            S))
        ( leq-sum-levy-base-index-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
          n
          S)
```

## Weight bounds for forced sums

```agda
module _
  (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ)
  where

  k-wfs : ℕ
  k-wfs = pr1 S

  χ-wfs : ℕ → bool
  χ-wfs = pr1 (pr2 S)

  extended-S-wfs : levy-base-index-sequence-macneille-ℝ
  extended-S-wfs =
    extend-levy-base-index-force-true-sequence-macneille-ℝ n S

  extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs :
    Fin (k-wfs +ℕ succ-ℕ n) → ℚ
  extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs i =
    selected-weight-levy-sequence-macneille-ℝ
      ( nat-Fin (k-wfs +ℕ succ-ℕ n) i)
      ( force-true-ℕ n χ-wfs (nat-Fin (k-wfs +ℕ succ-ℕ n) i))

  i-n-wfs : Fin (k-wfs +ℕ succ-ℕ n)
  i-n-wfs = mod-succ-ℕ (k-wfs +ℕ n) n

  abstract
    eq-nat-Fin-i-n-wfs-wfs :
      nat-Fin (k-wfs +ℕ succ-ℕ n) i-n-wfs ＝ n
    eq-nat-Fin-i-n-wfs-wfs =
      eq-cong-le-ℕ
        ( k-wfs +ℕ succ-ℕ n)
        ( nat-Fin (k-wfs +ℕ succ-ℕ n) i-n-wfs)
        ( n)
        ( strict-upper-bound-nat-Fin
          ( k-wfs +ℕ succ-ℕ n)
          ( i-n-wfs))
        ( concatenate-le-leq-ℕ
          { x = n}
          { y = succ-ℕ n}
          { z = k-wfs +ℕ succ-ℕ n}
          ( succ-le-ℕ n)
          ( leq-add-ℕ' (succ-ℕ n) k-wfs))
        ( cong-nat-mod-succ-ℕ
          ( k-wfs +ℕ n)
          ( n))

    eq-selected-value-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs :
      extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs i-n-wfs ＝
      weight-levy-sequence-macneille-ℝ n
    eq-selected-value-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs =
      ap
        ( λ m →
          selected-weight-levy-sequence-macneille-ℝ m (force-true-ℕ n χ-wfs m))
        ( eq-nat-Fin-i-n-wfs-wfs) ∙
      ( ind-bool
        ( λ b →
          is-true b →
          selected-weight-levy-sequence-macneille-ℝ n b ＝
          weight-levy-sequence-macneille-ℝ n)
        ( λ _ → refl)
        ( λ ())
        ( force-true-ℕ n χ-wfs n)
        ( is-true-force-true-self-ℕ n χ-wfs))

    leq-zero-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs :
      (i : Fin (k-wfs +ℕ succ-ℕ n)) →
      leq-ℚ
        zero-ℚ
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs i)
    leq-zero-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs
      i =
      ind-bool
        ( λ b →
          leq-ℚ
            zero-ℚ
            ( selected-weight-levy-sequence-macneille-ℝ
              ( nat-Fin
                ( k-wfs +ℕ succ-ℕ n)
                i)
              b))
        ( leq-zero-weight-levy-sequence-macneille-ℝ
          ( nat-Fin
            ( k-wfs +ℕ succ-ℕ n)
            i))
        ( refl-leq-ℚ zero-ℚ)
        ( force-true-ℕ
          n
          χ-wfs
          ( nat-Fin
            ( k-wfs +ℕ succ-ℕ n)
            i))

  abstract
    leq-weight-levy-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ :
      leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extended-S-wfs))
    leq-weight-levy-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ =
      transitive-leq-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs i-n-wfs)
        ( sum-fin-sequence-ℚ
          ( k-wfs +ℕ succ-ℕ n)
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs))
        ( leq-term-sum-fin-sequence-ℚ
          ( k-wfs +ℕ succ-ℕ n)
          ( extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs)
          ( leq-zero-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs)
          ( i-n-wfs))
        ( leq-eq-ℚ
          ( inv
            ( eq-selected-value-extended-fin-sequence-levy-base-index-force-true-sequence-macneille-ℝ-wfs-wfs)))
```

## Weight bounds for forced family elements

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (y : macneille-ℝ l)
  where

  abstract
    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ :
      (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f y S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              admissible-S
              not-y≤fn))
    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
      n S admissible-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S))
        ( leq-weight-levy-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
          n
          S)
```

## Admissibility at image indices

```agda
abstract
  is-false-admissible-index-image-levy-base-index-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) (x : macneille-ℝ l) (n : ℕ) →
    f n ＝ x →
    (S : levy-base-index-sequence-macneille-ℝ) →
    is-admissible-levy-base-index-sequence-macneille-ℝ f x S →
    is-false (pr1 (pr2 S) n)
  is-false-admissible-index-image-levy-base-index-sequence-macneille-ℝ
    f
    x
    n
    fn=x
    (k , (χ , χ-outside-k))
    admissible-S =
    is-false-is-not-true
      ( χ n)
      ( λ n∈S →
        admissible-S n n∈S
          ( tr
            ( leq-macneille-ℝ x)
            ( inv fn=x)
            ( refl-leq-macneille-ℝ x)))
```

## Adding forced weights

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
      n fn=x x≤y S admissible-S not-y≤fn =
      leq-raise-macneille-real-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ
            n
            S))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
          n
          S
          ( is-false-admissible-index-image-levy-base-index-sequence-macneille-ℝ
            f
            x
            n
            fn=x
            S
            admissible-S))

    leq-add-sum-levy-base-index-map-ℕ-weight-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x →
      (x≤y : leq-macneille-ℝ x y) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-add-sum-levy-base-index-map-ℕ-weight-endomap-levy-sequence-macneille-ℝ
      n fn=x x≤y S admissible-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ f y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
          n
          fn=x
          x≤y
          S
          admissible-S
          not-y≤fn)
```

## Forced upper-bound transport

```agda
module _
  {l : Level} (f : ℕ → macneille-ℝ l) (x y : macneille-ℝ l)
  where

  abstract
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-force-true-map-ℕ-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ) →
      (x≤y : leq-macneille-ℝ x y) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          x
          ( S ,
            admissible-S))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-force-true-map-ℕ-endomap-levy-sequence-macneille-ℝ
      n S x≤y admissible-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          x
          ( S ,
            admissible-S))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( leq-family-element-levy-base-index-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
          f
          x
          y
          n
          S
          x≤y
          admissible-S
          not-y≤fn)

    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-force-true-map-ℕ-endomap-levy-sequence-macneille-ℝ :
      (n : ℕ) (S : levy-base-index-sequence-macneille-ℝ) →
      (x≤y : leq-macneille-ℝ x y) →
      (admissible-S : is-admissible-levy-base-index-sequence-macneille-ℝ f x S) →
      (not-y≤fn : ¬ leq-macneille-ℝ y (f n)) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( weight-levy-sequence-macneille-ℝ n))
        ( endomap-levy-sequence-macneille-ℝ f y)
    leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-force-true-map-ℕ-endomap-levy-sequence-macneille-ℝ
      n S x≤y admissible-S not-y≤fn =
      transitive-leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( weight-levy-sequence-macneille-ℝ n))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          y
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( endomap-levy-sequence-macneille-ℝ f y)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ f y)
          ( family-of-elements-levy-sequence-macneille-ℝ f y)
          ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f y))
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
              f
              y
              n
              S
              ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
                f
                {x = x}
                {y = y}
                x≤y
                S
                admissible-S)
              not-y≤fn))
        ( leq-weight-levy-map-ℕ-family-element-extend-levy-base-index-force-true-sequence-macneille-ℝ
          f
          y
          n
          S
          ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ
            f
            {x = x}
            {y = y}
            x≤y
            S
            admissible-S)
          not-y≤fn)
```

## Strict positivity of weights

```agda
abstract
  le-zero-weight-levy-map-ℕ-ℚ :
    (n : ℕ) →
    le-ℚ zero-ℚ (weight-levy-sequence-macneille-ℝ n)
  le-zero-weight-levy-map-ℕ-ℚ n =
    le-zero-is-positive-ℚ (is-positive-power-ℚ⁺ n one-half-ℚ⁺)

  le-raise-zero-weight-levy-sequence-macneille-ℝ :
    {l : Level} (n : ℕ) →
    le-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-real-ℚ l (weight-levy-sequence-macneille-ℝ n))
  le-raise-zero-weight-levy-sequence-macneille-ℝ {l} n =
    le-raise-macneille-real-ℚ
      zero-ℚ
      ( weight-levy-sequence-macneille-ℝ n)
      ( le-zero-weight-levy-map-ℕ-ℚ n)
```

## Postfixpoints of the levy endomap

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
        ( pr1 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
        ( pr2 (has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x))
        ( raise-macneille-real-ℚ l (rational-ℕ 2))
        ( is-upper-bound-family-of-elements-levy-sequence-macneille-ℝ f x)

    is-postfixpoint-zero-endomap-levy-sequence-macneille-ℝ :
      is-postfixpoint-endomap-macneille-ℝ
        ( endomap-levy-sequence-macneille-ℝ f)
        ( raise-zero-macneille-ℝ l)
    is-postfixpoint-zero-endomap-levy-sequence-macneille-ℝ =
      is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( is-inhabited-indexing-type-levy-family-sequence-macneille-ℝ
          f
          ( raise-zero-macneille-ℝ l))
        ( family-of-elements-levy-sequence-macneille-ℝ
          f
          ( raise-zero-macneille-ℝ l))
        ( pr1
          ( has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ
            f
            ( raise-zero-macneille-ℝ l)))
        ( pr2
          ( has-upper-bound-family-of-elements-levy-sequence-macneille-ℝ
            f
            ( raise-zero-macneille-ℝ l)))
        ( ( zero-ℕ , ( λ _ → false) , λ _ _ → refl) ,
          λ _ ())

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

## Finite levy not-in-image argument

```agda
is-self-admissible-levy-base-index-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  levy-base-index-sequence-macneille-ℝ → UU l
is-self-admissible-levy-base-index-sequence-macneille-ℝ {l} f S =
  is-admissible-levy-base-index-sequence-macneille-ℝ f
    ( raise-macneille-real-ℚ l
      ( sum-levy-base-index-sequence-macneille-ℝ S))
    ( S)

indexing-type-self-admissible-levy-family-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) → UU l
indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f =
  Σ levy-base-index-sequence-macneille-ℝ
    ( is-self-admissible-levy-base-index-sequence-macneille-ℝ f)

family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  indexing-type-self-admissible-levy-family-sequence-macneille-ℝ f →
  macneille-ℝ l
family-of-elements-self-admissible-levy-sequence-macneille-ℝ {l} _ (S , _) =
  raise-macneille-real-ℚ l (sum-levy-base-index-sequence-macneille-ℝ S)

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
      ( sum-levy-base-index-sequence-macneille-ℝ S)
      ( rational-ℕ 2)
      ( leq-two-sum-levy-base-index-sequence-macneille-ℝ S)

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
    ( pr1 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
    ( pr2 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))

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
      ( pr1 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
      ( pr2 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))

  is-least-upper-bound-family-of-elements-at-level-point-self-admissible-levy-sequence-macneille-ℝ :
    {l : Level} (f : ℕ → macneille-ℝ l) →
    is-least-upper-bound-family-of-elements-at-level-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( point-self-admissible-levy-sequence-macneille-ℝ f)
  is-least-upper-bound-family-of-elements-at-level-point-self-admissible-levy-sequence-macneille-ℝ
    f =
    is-least-upper-bound-family-of-elements-at-level-is-least-upper-bound-family-of-elements-macneille-ℝ
      ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
      ( point-self-admissible-levy-sequence-macneille-ℝ f)
      ( is-least-upper-bound-family-of-elements-point-self-admissible-levy-sequence-macneille-ℝ
        ( f))

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
      ( pr1 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
      ( pr2 (has-upper-bound-family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
```

### Contradiction at the least upper bound

```agda

module _
  {l : Level} (f : ℕ → macneille-ℝ l)
  (let x0 = point-self-admissible-levy-sequence-macneille-ℝ f)
  where

  abstract
    leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ' :
      ( S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S))
        ( x0)
    leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ'
      S self-admissible-S =
      leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ f
        ( S , self-admissible-S)

    is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      is-false (pr1 (pr2 S) n)
    is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-admissible-S =
      is-false-admissible-index-image-levy-base-index-sequence-macneille-ℝ
        ( f)
        ( x0)
        ( n)
        ( fn=x0)
        ( S)
        ( is-admissible-leq-levy-base-index-sequence-macneille-ℝ f
          {x =
            raise-macneille-real-ℚ l
              ( sum-levy-base-index-sequence-macneille-ℝ S)}
          {y = x0}
          ( leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ'
            ( S)
            ( self-admissible-S))
          ( S)
          ( self-admissible-S))

    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      leq-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ
            n
            S))
    leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-admissible-S =
      leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
        ( n)
        ( S)
        ( is-false-self-admissible-index-at-image-point-self-admissible-levy-sequence-macneille-ℝ
          ( n)
          ( fn=x0)
          ( S)
          ( self-admissible-S))

    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      f n ＝ x0 →
      (S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
            weight-levy-sequence-macneille-ℝ n))
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ
            ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
    leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-admissible-S =
      leq-raise-macneille-real-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
          weight-levy-sequence-macneille-ℝ n)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S))
        ( leq-add-sum-levy-base-index-map-ℕ-weight-sum-extend-self-admissible-levy-sequence-macneille-ℝ
          n fn=x0 S self-admissible-S)

  abstract
    leq-sum-levy-base-index-map-ℕ-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      leq-macneille-ℝ
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ S))
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ
            ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
    leq-sum-levy-base-index-map-ℕ-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n S =
      leq-raise-macneille-real-ℚ
        ( sum-levy-base-index-sequence-macneille-ℝ S)
        ( sum-levy-base-index-sequence-macneille-ℝ
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ
            ( n)
            ( S)))
        ( leq-sum-levy-base-index-map-ℕ-sum-extend-levy-base-index-force-true-sequence-macneille-ℝ
          ( n)
          ( S))

  abstract
    is-self-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ-from-not-leq :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      ¬ ( leq-macneille-ℝ
          ( raise-macneille-real-ℚ l
            ( sum-levy-base-index-sequence-macneille-ℝ
              ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
          ( x0)) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f
        ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)
    is-self-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ-from-not-leq
      n fn=x0 S self-admissible-S not-extend-S≤x0 =
      is-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ
        ( f)
        ( raise-macneille-real-ℚ l
          ( sum-levy-base-index-sequence-macneille-ℝ
            ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
        ( n)
        ( S)
        ( λ m m∈S sum-extend-S≤fm →
          self-admissible-S m m∈S
            ( transitive-leq-macneille-ℝ
              ( raise-macneille-real-ℚ l
                ( sum-levy-base-index-sequence-macneille-ℝ S))
              ( raise-macneille-real-ℚ l
                ( sum-levy-base-index-sequence-macneille-ℝ
                  ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
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
                    ( sum-levy-base-index-sequence-macneille-ℝ
                      ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S))))
              ( fn=x0)
              ( sum-extend-S≤fn)))

    double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      is-self-admissible-levy-base-index-sequence-macneille-ℝ f S →
      ¬¬
        ( leq-macneille-ℝ
          ( raise-macneille-real-ℚ l
            ( sum-levy-base-index-sequence-macneille-ℝ
              ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S)))
          ( x0))
    double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-admissible-S not-extend-S≤x0 =
      not-extend-S≤x0
        ( leq-family-element-point-self-admissible-levy-sequence-macneille-ℝ f
          ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S ,
            is-self-admissible-extend-levy-base-index-force-true-sequence-macneille-ℝ-from-not-leq
              ( n)
              ( fn=x0)
              ( S)
              ( self-admissible-S)
              ( not-extend-S≤x0)))

  abstract
    leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      (S : levy-base-index-sequence-macneille-ℝ) →
      ( self-admissible-S :
        is-self-admissible-levy-base-index-sequence-macneille-ℝ f S) →
      leq-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( weight-levy-sequence-macneille-ℝ n)
          ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f)
          ( S , self-admissible-S))
        ( x0)
    leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 S self-admissible-S =
      let
        extend-S≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( sum-levy-base-index-sequence-macneille-ℝ
                ( extend-levy-base-index-force-true-sequence-macneille-ℝ
                  n
                  S)))
            ( x0)
        extend-S≤x0 =
          double-negation-elim-leq-left-raise-macneille-real-ℚ
            ( x0)
            ( sum-levy-base-index-sequence-macneille-ℝ
              ( extend-levy-base-index-force-true-sequence-macneille-ℝ n S))
            ( double-neg-leq-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
              ( n)
              ( fn=x0)
              ( S)
              ( self-admissible-S))

        add-sum-S+weight≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
                weight-levy-sequence-macneille-ℝ n))
            ( x0)
        add-sum-S+weight≤x0 =
          transitive-leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( sum-levy-base-index-sequence-macneille-ℝ S +ℚ
                weight-levy-sequence-macneille-ℝ n))
            ( raise-macneille-real-ℚ l
              ( sum-levy-base-index-sequence-macneille-ℝ
                ( extend-levy-base-index-force-true-sequence-macneille-ℝ
                  n
                  S)))
            ( x0)
            extend-S≤x0
            ( leq-add-sum-levy-base-index-map-ℕ-weight-family-element-extend-self-admissible-levy-sequence-macneille-ℝ
              ( n)
              ( fn=x0)
              ( S)
              ( self-admissible-S))

        add-weight+sum-S≤x0 :
          leq-macneille-ℝ
            ( raise-macneille-real-ℚ l
              ( weight-levy-sequence-macneille-ℝ n +ℚ
                sum-levy-base-index-sequence-macneille-ℝ S))
            ( x0)
        add-weight+sum-S≤x0 =
          tr
            ( λ z → leq-macneille-ℝ z x0)
            ( ap
              ( raise-macneille-real-ℚ l)
              ( commutative-add-ℚ
                ( sum-levy-base-index-sequence-macneille-ℝ S)
                ( weight-levy-sequence-macneille-ℝ n)))
            ( add-sum-S+weight≤x0)
      in
        tr
          ( λ z →
            leq-macneille-ℝ
              z
              x0)
          ( inv
            ( eq-right-translate-raise-macneille-real-ℚ'
              ( weight-levy-sequence-macneille-ℝ n)
              ( sum-levy-base-index-sequence-macneille-ℝ S)))
          add-weight+sum-S≤x0

    is-upper-bound-right-translate-family-of-elements-self-admissible-levy-sequence-macneille-ℝ :
      (n : ℕ) →
      (fn=x0 : f n ＝ x0) →
      is-upper-bound-family-of-elements-macneille-ℝ
        ( translate-family-right-macneille-real-ℚ
          ( weight-levy-sequence-macneille-ℝ n)
          ( family-of-elements-self-admissible-levy-sequence-macneille-ℝ f))
        x0
    is-upper-bound-right-translate-family-of-elements-self-admissible-levy-sequence-macneille-ℝ
      n fn=x0 (S , self-admissible-S) =
      leq-right-translate-family-element-point-self-admissible-levy-sequence-macneille-ℝ
        ( n)
        ( fn=x0)
        ( S)
        ( self-admissible-S)

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
          ( is-least-upper-bound-family-of-elements-at-level-point-self-admissible-levy-sequence-macneille-ℝ
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

### Final theorem

```agda
sequence-avoiding-point-macneille-ℝ :
  {l : Level} (f : ℕ → macneille-ℝ l) →
  Σ (macneille-ℝ l) (λ x0 → (n : ℕ) → f n ≠ x0)
sequence-avoiding-point-macneille-ℝ f =
  ( point-self-admissible-levy-sequence-macneille-ℝ f ,
    not-in-image-point-self-admissible-levy-sequence-macneille-ℝ f)
```

## References

{{#bibliography}}
