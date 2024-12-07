# Divisibility of natural numbers

```agda
module elementary-number-theory.divisibility-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

On this page we define the
{{#concept "divisibility" Disambiguation="natural numbers" Agda=div-ℕ WD="divisibility" WDID=Q5284415}}
relation on the [natural numbers](elementary-number-theory.natural-numbers.md).
A natural number `m` is said to **divide** a natural number `n` if there exists
a natural number `k` equipped with an
[identification](foundation-core.identifications.md) `km ＝ n`. Using the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory, we express divisibility as follows:

```text
  div-ℕ m n := Σ (k : ℕ), k *ℕ m ＝ n.
```

If `n` is a
[nonzero natural number](elementary-number-theory.nonzero-natural-numbers.md),
then the type `div-ℕ m n` is always a
[proposition](foundation-core.propositions.md) in the sense that the type
`div-ℕ m n` contains at most one element.

The divisibility relation is
[logically equivalent](foundation.logical-equivalences.md), though not
[equivalent](foundation-core.equivalences.md), to the
{{#concept "bounded divisibility" Disambiguation="natural numbers" Agda=bounded-div-ℕ}}
relation, which is defined by

```text
  bounded-div-ℕ m n := Σ (k : ℕ), (k ≤ n) × (k *ℕ m ＝ n).
```

The discrepancy between divisibility and bounded divisibility is manifested at
`(0 , 0)`. Note that `div-ℕ 0 0 ≃ ℕ`, while `bounded-div-ℕ 0 0` is
[contractible](foundation-core.contractible-types.md). For all other values we
have `div-ℕ m n ≃ bounded-div-ℕ m n`.

The notion of bounded divisibility has several advantages over ordinary
divisibility: Bounded divisibility is always a proposition, and the proof that
divisibility is decidable uses the proof that bounded divisibility is decidable.

## Definitions

### The divisibility relation on the natural numbers

```agda
module _
  (m n : ℕ)
  where

  div-ℕ : UU lzero
  div-ℕ = Σ ℕ (λ k → k *ℕ m ＝ n)

  quotient-div-ℕ : div-ℕ → ℕ
  quotient-div-ℕ = pr1

  eq-quotient-div-ℕ : (H : div-ℕ) → quotient-div-ℕ H *ℕ m ＝ n
  eq-quotient-div-ℕ = pr2

  eq-quotient-div-ℕ' : (H : div-ℕ) → m *ℕ quotient-div-ℕ H ＝ n
  eq-quotient-div-ℕ' H =
    commutative-mul-ℕ m (quotient-div-ℕ H) ∙ eq-quotient-div-ℕ H
```

### The bounded divisibility predicate

```agda
module _
  (m n : ℕ)
  where

  bounded-div-ℕ : UU lzero
  bounded-div-ℕ = Σ ℕ (λ k → (k ≤-ℕ n) × (k *ℕ m ＝ n))

  quotient-bounded-div-ℕ : bounded-div-ℕ → ℕ
  quotient-bounded-div-ℕ = pr1

  upper-bound-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H ≤-ℕ n
  upper-bound-quotient-bounded-div-ℕ H = pr1 (pr2 H)

  eq-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H *ℕ m ＝ n
  eq-quotient-bounded-div-ℕ H = pr2 (pr2 H)

  eq-quotient-bounded-div-ℕ' :
    (H : bounded-div-ℕ) → m *ℕ quotient-bounded-div-ℕ H ＝ n
  eq-quotient-bounded-div-ℕ' H =
    commutative-mul-ℕ m (quotient-bounded-div-ℕ H) ∙ eq-quotient-bounded-div-ℕ H

  div-bounded-div-ℕ : bounded-div-ℕ → div-ℕ m n
  pr1 (div-bounded-div-ℕ H) = quotient-bounded-div-ℕ H
  pr2 (div-bounded-div-ℕ H) = eq-quotient-bounded-div-ℕ H
```

## Properties

### Concatenating equality and divisibility

```agda
concatenate-eq-div-ℕ :
  {x y z : ℕ} → x ＝ y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = p

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → y ＝ z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → div-ℕ y z → z ＝ w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = p
```

### The quotient of `n` by a number `m` it is divisible by also divides `n`

```agda
div-quotient-div-ℕ :
  (m n : ℕ) (H : div-ℕ m n) → div-ℕ (quotient-div-ℕ m n H) n
pr1 (div-quotient-div-ℕ m n (u , p)) = m
pr2 (div-quotient-div-ℕ m n (u , p)) = commutative-mul-ℕ m u ∙ p
```

### The quotients of a natural number `n` by two natural numbers `c` and `d` are equal if `c` and `d` are equal

```agda
eq-quotient-div-eq-div-ℕ :
  (c d n : ℕ) → is-nonzero-ℕ c → c ＝ d →
  (H : div-ℕ c n) → (I : div-ℕ d n) →
  quotient-div-ℕ c n H ＝ quotient-div-ℕ d n I
eq-quotient-div-eq-div-ℕ c d n N p H I =
  is-injective-left-mul-ℕ c N
    ( tr
      ( λ x → c *ℕ quotient-div-ℕ c n H ＝ x *ℕ quotient-div-ℕ d n I)
      ( inv p)
      ( commutative-mul-ℕ c (quotient-div-ℕ c n H) ∙
        eq-quotient-div-ℕ c n H ∙
        inv (eq-quotient-div-ℕ d n I) ∙
        commutative-mul-ℕ (quotient-div-ℕ d n I) d))
```

### If `x` is nonzero and `d | x`, then `d ≤ x`

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (pair (succ-ℕ k) p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (pair y refl) = leq-div-succ-ℕ d y H

leq-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → leq-ℕ (quotient-div-ℕ d x H) x
leq-quotient-div-ℕ d x f H =
  leq-div-ℕ (quotient-div-ℕ d x H) x f (div-quotient-div-ℕ d x H)

leq-quotient-div-ℕ' :
  (d x : ℕ) → is-nonzero-ℕ d → (H : div-ℕ d x) → leq-ℕ (quotient-div-ℕ d x H) x
leq-quotient-div-ℕ' d zero-ℕ f (zero-ℕ , p) = star
leq-quotient-div-ℕ' d zero-ℕ f (succ-ℕ n , p) =
  f (is-zero-right-is-zero-add-ℕ _ d p)
leq-quotient-div-ℕ' d (succ-ℕ x) f H =
  leq-quotient-div-ℕ d (succ-ℕ x) (is-nonzero-succ-ℕ x) H
```

### If `x` is nonzero, if `d | x` and `d ≠ x`, then `d < x`

```agda
le-div-succ-ℕ :
  (d x : ℕ) → div-ℕ d (succ-ℕ x) → d ≠ succ-ℕ x → le-ℕ d (succ-ℕ x)
le-div-succ-ℕ d x H f = le-leq-neq-ℕ (leq-div-succ-ℕ d x H) f

le-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → d ≠ x → le-ℕ d x
le-div-ℕ d x H K f = le-leq-neq-ℕ (leq-div-ℕ d x H K) f
```

### Divisibility is logically equivalent to bounded divisibility

```agda
bounded-div-div-ℕ : (m n : ℕ) → div-ℕ m n → bounded-div-ℕ m n
bounded-div-div-ℕ m zero-ℕ (q , p) = (0 , refl-leq-ℕ 0 , left-zero-law-mul-ℕ m)
bounded-div-div-ℕ m (succ-ℕ n) (q , p) =
  ( q , leq-quotient-div-ℕ m (succ-ℕ n) (is-nonzero-succ-ℕ n) (q , p) , p)

logical-equivalence-bounded-div-div-ℕ :
  (m n : ℕ) → bounded-div-ℕ m n ↔ div-ℕ m n
pr1 (logical-equivalence-bounded-div-div-ℕ m n) =
  div-bounded-div-ℕ m n
pr2 (logical-equivalence-bounded-div-div-ℕ m n) =
  bounded-div-div-ℕ m n
```

### Bounded divisibility is decidable

```agda
is-decidable-bounded-div-ℕ :
  (m n : ℕ) → is-decidable (bounded-div-ℕ m n)
is-decidable-bounded-div-ℕ m n =
  is-decidable-bounded-Σ-ℕ'
    ( n)
    ( λ x → mul-ℕ x m ＝ n)
    ( λ x → has-decidable-equality-ℕ (mul-ℕ x m) n)
```

### Divisibility is decidable

```agda
is-decidable-div-ℕ :
  (m n : ℕ) → is-decidable (div-ℕ m n)
is-decidable-div-ℕ m n =
  is-decidable-iff
    ( div-bounded-div-ℕ m n)
    ( bounded-div-div-ℕ m n)
    ( is-decidable-bounded-div-ℕ m n)
```

### Divisibility is a property except at `(0,0)`

```agda
is-prop-div-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k + is-nonzero-ℕ x → is-prop (div-ℕ k x)
is-prop-div-ℕ k x (inl H) = is-prop-map-is-emb (is-emb-right-mul-ℕ k H) x
is-prop-div-ℕ zero-ℕ x (inr H) =
  is-prop-is-proof-irrelevant
    ( λ (q , p) → ex-falso (H (inv p ∙ right-zero-law-mul-ℕ q)))
is-prop-div-ℕ (succ-ℕ k) x (inr H) =
  is-prop-map-is-emb (is-emb-right-mul-ℕ (succ-ℕ k) (is-nonzero-succ-ℕ k)) x

div-ℕ-Decidable-Prop : (d x : ℕ) → is-nonzero-ℕ d → Decidable-Prop lzero
pr1 (div-ℕ-Decidable-Prop d x H) = div-ℕ d x
pr1 (pr2 (div-ℕ-Decidable-Prop d x H)) = is-prop-div-ℕ d x (inl H)
pr2 (pr2 (div-ℕ-Decidable-Prop d x H)) = is-decidable-div-ℕ d x
```

### Bounded divisibility is a property

```agda
abstract
  is-prop-bounded-div-ℕ :
    (k n : ℕ) → is-prop (bounded-div-ℕ k n)
  is-prop-bounded-div-ℕ zero-ℕ n =
    is-prop-all-elements-equal
      ( λ (q , b , p) (q' , b' , p') →
        eq-type-subtype
          ( λ u → product-Prop (leq-ℕ-Prop u n) (Id-Prop ℕ-Set _ _))
          ( is-zero-leq-zero-ℕ q
            ( concatenate-leq-eq-ℕ q b (inv p ∙ right-zero-law-mul-ℕ q)) ∙
            inv
              ( is-zero-leq-zero-ℕ q'
                ( concatenate-leq-eq-ℕ q' b'
                  ( inv p' ∙ right-zero-law-mul-ℕ q')))))
  is-prop-bounded-div-ℕ (succ-ℕ k) n =
    is-prop-equiv
      ( equiv-right-swap-Σ ∘e inv-associative-Σ ℕ (λ x → x ≤-ℕ n) _)
      ( is-prop-Σ
        ( is-prop-div-ℕ (succ-ℕ k) n (inl (is-nonzero-succ-ℕ k)))
        ( λ (x , H) → is-prop-leq-ℕ x n))

bounded-div-ℕ-Prop : (k n : ℕ) → Prop lzero
pr1 (bounded-div-ℕ-Prop k n) = bounded-div-ℕ k n
pr2 (bounded-div-ℕ-Prop k n) = is-prop-bounded-div-ℕ k n

bounded-div-ℕ-Decidable-Prop : (k n : ℕ) → Decidable-Prop lzero
pr1 (bounded-div-ℕ-Decidable-Prop k n) = bounded-div-ℕ k n
pr1 (pr2 (bounded-div-ℕ-Decidable-Prop k n)) = is-prop-bounded-div-ℕ k n
pr2 (pr2 (bounded-div-ℕ-Decidable-Prop k n)) = is-decidable-bounded-div-ℕ k n
```

### The divisibility relation is a partial order on the natural numbers

The [poset](order-theory.posets.md) of natural numbers ordered by divisibility
is defined in
[`elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility`](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

```agda
refl-div-ℕ : is-reflexive div-ℕ
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

antisymmetric-div-ℕ : is-antisymmetric div-ℕ
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (pair k p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (pair l q) =
  inv q ∙ right-zero-law-mul-ℕ l
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (pair k p) (pair l q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap
      ( _*ℕ (succ-ℕ x))
      ( inv
        ( is-one-right-is-one-mul-ℕ l k
          ( is-one-is-left-unit-mul-ℕ (l *ℕ k) x
            ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
              ( ap (l *ℕ_) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ : is-transitive div-ℕ
pr1 (transitive-div-ℕ x y z (pair l q) (pair k p)) = l *ℕ k
pr2 (transitive-div-ℕ x y z (pair l q) (pair k p)) =
  associative-mul-ℕ l k x ∙ (ap (l *ℕ_) p ∙ q)
```

### `1` divides any number

```agda
div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = div-one-ℕ x
```

### `x | 1` implies `x ＝ 1`

```agda
is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)
```

### Any number divides `0`

```agda
div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = 0
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k
```

### `0 | x` implies `x = 0` and `x | 1` implies `x = 1`

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d
```

### Any divisor of a nonzero number is nonzero

```agda
is-nonzero-div-ℕ :
  (d x : ℕ) → div-ℕ d x → is-nonzero-ℕ x → is-nonzero-ℕ d
is-nonzero-div-ℕ .zero-ℕ x H K refl = K (is-zero-div-zero-ℕ x H)
```

### Any divisor of a number at least `1` is at least `1`

```agda
leq-one-div-ℕ :
  (d x : ℕ) → div-ℕ d x → leq-ℕ 1 x → leq-ℕ 1 d
leq-one-div-ℕ d x H L =
  leq-one-is-nonzero-ℕ d (is-nonzero-div-ℕ d x H (is-nonzero-leq-one-ℕ x L))
```

### If `x < d` and `d | x`, then `x` must be `0`

```agda
is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (pair (succ-ℕ k) p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (k *ℕ d)) p))
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (k *ℕ y)
div-mul-ℕ k x y H =
  transitive-div-ℕ x y (k *ℕ y) (pair k refl) H

div-mul-ℕ' :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (y *ℕ k)
div-mul-ℕ' k x y H =
  tr (div-ℕ x) (commutative-mul-ℕ k y) (div-mul-ℕ k x y H)
```

### A 3-for-2 property of division with respect to addition

```agda
div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (x +ℕ y)
pr1 (div-add-ℕ d x y (pair n p) (pair m q)) = n +ℕ m
pr2 (div-add-ℕ d x y (pair n p) (pair m q)) =
  ( right-distributive-mul-add-ℕ n m d) ∙
  ( ap-add-ℕ p q)

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (x +ℕ y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (pair m q) (pair n p) =
  pair zero-ℕ
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (x +ℕ_) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (pair m q) (pair n p)) =
  is-injective-right-add-ℕ (m *ℕ (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( m *ℕ (succ-ℕ d))
            ( (dist-ℕ m n) *ℕ (succ-ℕ d))))) ∙
      ( ( ap
          ( _*ℕ (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( reflects-order-mul-ℕ d m n
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (x +ℕ_) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (x +ℕ y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```

### If `d` divides both `x` and `x + 1`, then `d ＝ 1`

```agda
is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (k *ℕ x) (k *ℕ y)
pr1 (preserves-div-mul-ℕ k x y (pair q p)) = q
pr2 (preserves-div-mul-ℕ k x y (pair q p)) =
  ( inv (associative-mul-ℕ q k x)) ∙
    ( ( ap (_*ℕ x) (commutative-mul-ℕ q k)) ∙
      ( ( associative-mul-ℕ k q x) ∙
        ( ap (k *ℕ_) p)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℕ :
  (k x y : ℕ) → is-nonzero-ℕ k → div-ℕ (k *ℕ x) (k *ℕ y) → div-ℕ x y
pr1 (reflects-div-mul-ℕ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℕ k x y H (pair q p)) =
  is-injective-left-mul-ℕ k H
    ( ( inv (associative-mul-ℕ k q x)) ∙
      ( ( ap (_*ℕ x) (commutative-mul-ℕ k q)) ∙
        ( ( associative-mul-ℕ q k x) ∙
          ( p))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) → is-nonzero-ℕ d →
  div-ℕ (d *ℕ x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y d H f K =
  reflects-div-mul-ℕ d x
    ( quotient-div-ℕ d y H)
    ( f)
    ( tr (div-ℕ (d *ℕ x)) (inv (eq-quotient-div-ℕ' d y H)) K)

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (d *ℕ x) y
div-div-quotient-div-ℕ x y d H K =
  tr
    ( div-ℕ (d *ℕ x))
    ( eq-quotient-div-ℕ' d y H)
    ( preserves-div-mul-ℕ d x (quotient-div-ℕ d y H) K)
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {.(k *ℕ d)} (pair k refl) =
  is-nonzero-left-factor-mul-ℕ k d
```

### If `d` divides a number `1 ≤ x`, then `1 ≤ x/d`

```agda
leq-one-quotient-div-ℕ :
  (d x : ℕ) (H : div-ℕ d x) → leq-ℕ 1 x → leq-ℕ 1 (quotient-div-ℕ d x H)
leq-one-quotient-div-ℕ d x H K =
  leq-one-div-ℕ
    ( quotient-div-ℕ d x H)
    ( x)
    ( div-quotient-div-ℕ d x H)
    ( K)
```

### `a/a ＝ 1`

```agda
is-idempotent-quotient-div-ℕ :
  (a : ℕ) → is-nonzero-ℕ a → (H : div-ℕ a a) → is-one-ℕ (quotient-div-ℕ a a H)
is-idempotent-quotient-div-ℕ zero-ℕ nz (u , p) = ex-falso (nz refl)
is-idempotent-quotient-div-ℕ (succ-ℕ a) nz (u , p) =
  is-one-is-left-unit-mul-ℕ u a p
```

### If `b` divides `a` and `c` divides `b` and `c` is nonzero, then `a/b · b/c ＝ a/c`

```agda
simplify-mul-quotient-div-ℕ :
  {a b c : ℕ} → is-nonzero-ℕ c →
  (H : div-ℕ b a) (K : div-ℕ c b) (L : div-ℕ c a) →
  ( (quotient-div-ℕ b a H) *ℕ (quotient-div-ℕ c b K)) ＝
  ( quotient-div-ℕ c a L)
simplify-mul-quotient-div-ℕ {a} {b} {c} nz H K L =
  is-injective-right-mul-ℕ c nz
    ( equational-reasoning
      (a/b *ℕ b/c) *ℕ c
      ＝ a/b *ℕ (b/c *ℕ c)
        by associative-mul-ℕ a/b b/c c
      ＝ a/b *ℕ b
        by ap (a/b *ℕ_) (eq-quotient-div-ℕ c b K)
      ＝ a
        by eq-quotient-div-ℕ b a H
      ＝ a/c *ℕ c
        by inv (eq-quotient-div-ℕ c a L))
  where
  a/b : ℕ
  a/b = quotient-div-ℕ b a H
  b/c : ℕ
  b/c = quotient-div-ℕ c b K
  a/c : ℕ
  a/c = quotient-div-ℕ c a L
```

### If `d | a` and `d` is nonzero, then `x | a/d` if and only if `xd | a`

```agda
simplify-div-quotient-div-ℕ :
  {a d x : ℕ} → is-nonzero-ℕ d → (H : div-ℕ d a) →
  (div-ℕ x (quotient-div-ℕ d a H)) ↔ (div-ℕ (x *ℕ d) a)
pr1 (pr1 (simplify-div-quotient-div-ℕ nz H) (u , p)) = u
pr2 (pr1 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) =
  equational-reasoning
    u *ℕ (x *ℕ d)
    ＝ (u *ℕ x) *ℕ d
      by inv (associative-mul-ℕ u x d)
    ＝ (quotient-div-ℕ d a H) *ℕ d
      by ap (_*ℕ d) p
    ＝ a
      by eq-quotient-div-ℕ d a H
pr1 (pr2 (simplify-div-quotient-div-ℕ nz H) (u , p)) = u
pr2 (pr2 (simplify-div-quotient-div-ℕ {a} {d} {x} nz H) (u , p)) =
  is-injective-right-mul-ℕ d nz
    ( equational-reasoning
        (u *ℕ x) *ℕ d
        ＝ u *ℕ (x *ℕ d)
          by associative-mul-ℕ u x d
        ＝ a
          by p
        ＝ (quotient-div-ℕ d a H) *ℕ d
          by inv (eq-quotient-div-ℕ d a H))
```

### Suppose `H : b | a` and `K : c | b`, where `c` is nonzero. If `d` divides `b/c` then `d` divides `a/c`

```agda
div-quotient-div-div-quotient-div-ℕ :
  {a b c d : ℕ} → is-nonzero-ℕ c → (H : div-ℕ b a)
  (K : div-ℕ c b) (L : div-ℕ c a) →
  div-ℕ d (quotient-div-ℕ c b K) →
  div-ℕ d (quotient-div-ℕ c a L)
div-quotient-div-div-quotient-div-ℕ {a} {b} {c} {d} nz H K L M =
  tr
    ( div-ℕ d)
    ( simplify-mul-quotient-div-ℕ nz H K L)
    ( div-mul-ℕ
      ( quotient-div-ℕ b a H)
      ( d)
      ( quotient-div-ℕ c b K)
      ( M))
```

### If `x` is nonzero and `d | x`, then `x/d ＝ 1` if and only if `d ＝ x`

```agda
is-one-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → (d ＝ x) →
  is-one-ℕ (quotient-div-ℕ d x H)
is-one-quotient-div-ℕ d .d f H refl = is-idempotent-quotient-div-ℕ d f H

eq-is-one-quotient-div-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ (quotient-div-ℕ d x H) → d ＝ x
eq-is-one-quotient-div-ℕ d x (.1 , q) refl = inv (left-unit-law-mul-ℕ d) ∙ q
```

### If `x` is nonzero and `d | x`, then `x/d ＝ x` if and only if `d ＝ 1`

```agda
compute-quotient-div-is-one-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ d → quotient-div-ℕ d x H ＝ x
compute-quotient-div-is-one-ℕ .1 x (u , q) refl =
  inv (right-unit-law-mul-ℕ u) ∙ q

is-one-divisor-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) →
  quotient-div-ℕ d x H ＝ x → is-one-ℕ d
is-one-divisor-ℕ d x f (.x , q) refl =
  is-injective-left-mul-ℕ x f (q ∙ inv (right-unit-law-mul-ℕ x))
```

### If `x` is nonzero and `d | x` is a nontrivial divisor, then `x/d < x`

```agda
le-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → ¬ (is-one-ℕ d) →
  le-ℕ (quotient-div-ℕ d x H) x
le-quotient-div-ℕ d x f H g =
  map-left-unit-law-coproduct-is-empty
    ( quotient-div-ℕ d x H ＝ x)
    ( le-ℕ (quotient-div-ℕ d x H) x)
    ( map-neg (is-one-divisor-ℕ d x f H) g)
    ( eq-or-le-leq-ℕ
      ( quotient-div-ℕ d x H)
      ( x)
      ( leq-quotient-div-ℕ d x f H))
```
