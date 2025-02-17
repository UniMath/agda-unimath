# Introduction to homotopy type theory

This file collects references to formalization of constructions, propositions,
theorems and exercises from {{#cite Rij22}}.

```agda
module literature.introduction-to-homotopy-type-theory where

open import foundation.universe-levels
```

The first two sections introduce the metatheory of dependent type theories,
which correspond to built-in features of Agda.

## 3 The natural numbers

### 3.1 The formal specification of the type of natural numbers

```agda
open import elementary-number-theory.natural-numbers using
  ( ℕ -- the ℕ formation rule ⊢ ℕ type
  ; zero-ℕ -- the zero element
  ; succ-ℕ -- the successor function
  ; ind-ℕ -- the induction principle
  )
```

### 3.2 Addition on the natural numbers

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ)
```

### 3.3 Pattern matching

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( Fibonacci-ℕ)
```

### Exercises

**Exercise 3.1.** Multiplication and exponentiation.

```agda
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.exponentiation-natural-numbers using
  ( exp-ℕ)
```

**Exercise 3.2.** Minimum and maximum.

```agda
open import elementary-number-theory.minimum-natural-numbers using
  ( min-ℕ)
open import elementary-number-theory.maximum-natural-numbers using
  ( max-ℕ)
```

**Exercise 3.3.** Triangular numbers and factorial.

```agda
open import elementary-number-theory.triangular-numbers using
  ( triangular-number-ℕ)
open import elementary-number-theory.factorials using
  ( factorial-ℕ)
```

**Exercise 3.4.** Binomial coefficients.

```agda
open import elementary-number-theory.binomial-coefficients using
  ( binomial-coefficient-ℕ
  ; is-zero-binomial-coefficient-ℕ)
```

**Exercise 3.5.** Fibonacci sequence using the induction principle of natural
numbers.

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( Fibo)
```

**Exercise 3.6.** Division by two using pattern matching and induction.

> TODO

## 4 More inductive types

### 4.2 The unit type

```agda
open import foundation.unit-type using
  ( unit
  ; star
  ; ind-unit
  ; point)
```

### 4.3 The empty type

**Definition 4.3.1.** The empty type.

```agda
open import foundation.empty-types using
  ( empty
  ; ind-empty
  ; ex-falso)
```

**Definition 4.3.2.** Negation of types.

```agda
open import foundation.negation using
  ( ¬_)
open import foundation.empty-types using
  ( is-empty)
```

**Proposition 4.3.4** Contrapositives.

```agda
open import foundation.negation using
  ( map-neg)
```

### 4.4 Coproducts

**Definition 4.4.1.** Coproducts of types.

```agda
open import foundation.coproduct-types using
  ( _+_
  ; inl
  ; inr
  ; ind-coproduct
  ; rec-coproduct)
```

**Remark 4.4.2.** Coproducts of functions.

```agda
open import foundation.functoriality-coproduct-types using
  ( map-coproduct)
```

**Proposition 4.4.3.** Projections from coproducts with an empty type.

```agda
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coproduct-is-empty)
```

### 4.5 The type of integers

**Definition 4.5.1.** The integers.

```agda
open import elementary-number-theory.integers using
  ( ℤ
  ; in-pos-ℤ
  ; in-neg-ℤ
  ; neg-one-ℤ
  ; zero-ℤ
  ; one-ℤ)
```

**Remark 4.5.2.** The induction principle of integers.

```agda
open import elementary-number-theory.integers using
  ( ind-ℤ)
```

**Definition 4.5.3.** The successor function on integers.

```agda
open import elementary-number-theory.integers using
  ( succ-ℤ)
```

### 4.6 Dependent pair types

**Definition 4.6.1.** The dependent pair type.

Note that the library defines the type of dependent pairs as a _record_ as
opposed to an inductive type. This allows us to instruct Agda to add a
judgmental eta law for pairs.

```agda
open import foundation.dependent-pair-types using
  ( Σ
  ; pair ; _,_
  ; ind-Σ)
```

**Definition 4.6.2.** Projection maps.

```agda
open import foundation.dependent-pair-types using
  ( pr1
  ; pr2)
```

**Remark 4.6.3.** Currying.

```agda
open import foundation.dependent-pair-types using
  ( ev-pair)
```

**Definition 4.6.4.** The cartesian product.

```agda
open import foundation.cartesian-product-types using
  ( _×_
  ; ind-product)
```

### Exercises

**Exercise 4.1.** Predecessor, addition, negation and multiplication on
integers.

```agda
open import elementary-number-theory.integers using
  ( pred-ℤ)
open import elementary-number-theory.addition-integers using
  ( add-ℤ)
open import elementary-number-theory.integers using
  ( neg-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ)
```

**Exercise 4.2.** Boolean negation, conjunction and disjunction.

```agda
open import foundation.booleans using
  ( bool
  ; ind-bool
  ; neg-bool
  ; conjunction-bool
  ; disjunction-bool)
```

**Exercise 4.3.** Double negation.

Note that we call bi-implications _logical equivalences_ in the library.

```agda
open import foundation.logical-equivalences using
  ( _↔_)
-- TODO: Put this somewhere
neg-elim : {l : Level} (P : UU l) → ¬ (P × ¬ P)
neg-elim P (pair p np) = np p
open import foundation.negation using
  ( no-fixed-points-neg -- ¬(P ↔ ¬P)
  )
open import foundation.double-negation using
  ( intro-double-negation -- P → ¬¬P
  ; map-double-negation -- (P → Q) → (¬¬P → ¬¬Q)
  ; double-negation-extend -- (P → ¬¬Q) → (¬¬P → ¬¬Q)
  )
open import foundation.double-negation using
  ( double-negation-double-negation-elim -- ¬¬(¬¬P → P)
  ; double-negation-Peirces-law -- ¬¬(((P → Q) → P) → P)
  ; double-negation-linearity-implication -- ¬¬((P → Q) + (Q → P))
  ; double-negation-decidability -- ¬¬ (P + ¬ P)
  )
open import foundation.decidable-types using
  ( double-negation-elim-is-decidable -- (P + ¬P) → (¬¬P → P)
  -- TODO: ¬¬(Q → P) ↔ ((P + ¬P) → (Q → P))
  )
open import logic.double-negation-elimination using
  ( double-negation-elim-neg -- ¬¬(¬ P) → P
  ; double-negation-elim-exp-neg-neg -- ¬¬(P → ¬¬Q) → (P → ¬¬Q)
  ; double-negation-elim-product
  )
has-double-negation-elim-prod-neg-neg :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬ ¬ ((¬ ¬ P) × (¬ ¬ Q)) → (¬ ¬ P) × (¬ ¬ Q)
has-double-negation-elim-prod-neg-neg {P = P} {Q = Q} =
  double-negation-elim-product
    ( double-negation-elim-neg (¬ P))
    ( double-negation-elim-neg (¬ Q))
-- TODO: f
```

**Exercise 4.4.** Lists.

```agda
open import lists.lists using
  ( list
  ; nil
  ; cons
  ; ind-list
  ; fold-list)
open import lists.functoriality-lists using
  ( map-list)
open import lists.lists using
  ( length-list)
open import elementary-number-theory.sums-of-natural-numbers using
  ( sum-list-ℕ)
open import elementary-number-theory.products-of-natural-numbers using
  ( product-list-ℕ)
open import lists.concatenation-lists using
  ( concat-list)
open import lists.flattening-lists using
  ( flatten-list)
open import lists.reversing-lists using
  ( reverse-list)
```

## 5 Identity types

### 5.1 The inductive definition of identity types

```agda
open import foundation.identity-types using
  ( _＝_
  ; refl
  ; ind-Id)
```

### 5.2 The groupoidal structure of types

**Definition 5.2.1.** Concatenation of identifications.

```agda
open import foundation.identity-types using
  ( concat)
```

**Definition 5.2.2.** Inverse operation.

```agda
open import foundation.identity-types using
  ( inv)
```

**Definition 5.2.4.** Associator.

```agda
open import foundation.identity-types using
  ( assoc)
```

**Definition 5.2.5.** Unit law operations.

```agda
open import foundation.identity-types using
  ( left-unit
  ; right-unit)
```

**Definition 5.2.5.** Inverse law operations.

```agda
open import foundation.identity-types using
  ( left-inv
  ; right-inv)
```

### 5.3 The action on identifications of functions

**Definition 5.3.1.** Action on paths.

Note that the operations `ap-id` and `ap-comp` provide identifications in the
inverse direction from the ones in the book.

```agda
open import foundation.action-on-identifications-functions using
  ( ap
  ; ap-id
  ; ap-comp)
```

**Definition 5.3.2.** Preservation rules.

```agda
open import foundation.action-on-identifications-functions using
  ( ap-refl
  ; ap-inv
  ; ap-concat)
```

### 5.4 Transport

**Definition 5.4.1.** Transport.

```agda
open import foundation.transport-along-identifications using
  ( tr)
```

**Definition 5.4.2.** Dependent action on paths.

```agda
open import foundation.action-on-identifications-dependent-functions using
  ( apd)
```

### 5.5 The uniqueness of `refl`

```agda
open import foundation.torsorial-type-families using
  ( is-torsorial-Id)
```

### 5.6 The laws of addition on ℕ

**Proposition 5.6.1.** Unit laws.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( left-unit-law-add-ℕ
  ; right-unit-law-add-ℕ)
```

**Proposition 5.6.2.** Successor laws.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( left-successor-law-add-ℕ
  ; right-successor-law-add-ℕ)
```

**Proposition 5.6.3.** Associativity.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( associative-add-ℕ)
```

**Proposition 5.6.4.** Commutativity.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( commutative-add-ℕ)
```

### Exercises

**Exercise 5.1.** Distributivity of inversion over concatenation.

```agda
open import foundation.identity-types using
  ( distributive-inv-concat)
```

**Exercise 5.2.** Transposing concatenation.

```agda
open import foundation.identity-types using
  ( left-transpose-eq-concat
  ; right-transpose-eq-concat)
```

**Exercise 5.3.** Path lifting.

```agda
open import foundation.equality-dependent-pair-types using
  ( eq-pair-eq-base)
```

**Exercise 5.4.** Mac Lane pentagon.

```agda
open import foundation.identity-types using
  ( mac-lane-pentagon)
```

**Exercise 5.5.** Semiring laws for addition and multiplication of natural
numbers.

```agda
open import elementary-number-theory.multiplication-natural-numbers using
  ( right-zero-law-mul-ℕ -- m * 0 = 0
  ; left-zero-law-mul-ℕ -- 0 * m = 0
  ; right-unit-law-mul-ℕ -- m * 1 = m
  ; left-unit-law-mul-ℕ -- 1 * m = m
  ; right-successor-law-mul-ℕ -- m * (succ n) = m + m * n
  ; left-successor-law-mul-ℕ -- (succ m) * n = m * n + n
  )
open import elementary-number-theory.multiplication-natural-numbers using
  ( commutative-mul-ℕ -- m * n = n * m
  )
open import elementary-number-theory.multiplication-natural-numbers using
  ( left-distributive-mul-add-ℕ -- m * (n + k) = m * n + m * k
  ; right-distributive-mul-add-ℕ -- (m + n) * k = m * k + n * k
  )
open import elementary-number-theory.multiplication-natural-numbers using
  ( associative-mul-ℕ -- (m * n) * k = m * (n * k)
  )
```

**Exercise 5.6.** Successor and predecessor operations on integers are mutual
inverses.

```agda
open import elementary-number-theory.integers using
  ( is-section-pred-ℤ -- (succ (pred k)) = k
  ; is-retraction-pred-ℤ -- (pred (succ k)) = k
  )
```

**Exercise 5.7.** Abelian group laws for addition of integers.

```agda
open import elementary-number-theory.addition-integers using
  ( left-unit-law-add-ℤ -- 0 + x = x
  ; right-unit-law-add-ℤ -- x + 0 = x
  )
open import elementary-number-theory.addition-integers using
  ( left-predecessor-law-add-ℤ -- pred x + y = pred (x + y)
  ; right-predecessor-law-add-ℤ -- x + pred y = pred (x + y)
  ; left-successor-law-add-ℤ -- succ x + y = succ (x + y)
  ; right-successor-law-add-ℤ -- x + succ y = succ (x + y)
  )
open import elementary-number-theory.addition-integers using
  ( associative-add-ℤ -- (x + y) + z = x + (y + z)
  ; commutative-add-ℤ -- x + y = y + x
  )
open import elementary-number-theory.addition-integers using
  ( left-inverse-law-add-ℤ -- (-x) + x = 0
  ; right-inverse-law-add-ℤ -- x + (-x) = 0
  )
```

**Exercise 5.8.** Ring laws for multiplication of integers.

```agda
open import elementary-number-theory.multiplication-integers using
  ( left-zero-law-mul-ℤ -- 0 * x = x
  ; right-zero-law-mul-ℤ -- x * 0 = x
  ; left-unit-law-mul-ℤ -- 1 * x = x
  ; right-unit-law-mul-ℤ -- x * 1 = x
  )
open import elementary-number-theory.multiplication-integers using
  ( left-predecessor-law-mul-ℤ' -- pred x * y = x * y - y
  ; right-predecessor-law-mul-ℤ' -- x * pred y = x * y - x
  ; left-successor-law-mul-ℤ' -- succ x * y = x * y + y
  ; right-successor-law-mul-ℤ' -- x * succ y = x * y + x TODO: report typo in the book
  )
open import elementary-number-theory.multiplication-integers using
  ( associative-mul-ℤ -- (x * y) * z = x * (y * z)
  ; commutative-mul-ℤ -- x * y = y * x
  )
```

## 6 Universes

TODO: Properly explain how this section relates to Agda's Levels and Sets.

### 6.2 Assuming enough universes

**Postulate 6.2.1.** There are enough universes.

The postulate is metatheoretical, so it doesn't have a corresponding term.
Instead we are guaranteed to have enough universes by Agda's implementation.

**Definition 6.2.2.** The base universe.

```agda
open import foundation.universe-levels using
  ( lzero)
```

**Definition 6.2.3.** The successor universe.

```agda
open import foundation.universe-levels using
  ( lsuc)
```

**Definition 6.2.5.** The join of two universes.

```agda
open import foundation.universe-levels using
  ( _⊔_)
```

Note that while in the book `(𝒰 ⊔ 𝒱) ⊔ 𝒲` and `𝒰 ⊔ (𝒱 ⊔ 𝒲)` are a priori
unrelated, Agda considers them equal.

### 6.3 Observational equality of the natural numbers

**Definition 6.3.1.** Observational equality of ℕ.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( Eq-ℕ)
```

**Lemma 6.3.2.** Observational equality of ℕ is reflexive.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( refl-Eq-ℕ)
```

**Proposition 6.3.3.** Logical equivalence of observational equality of ℕ and
identifications.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( Eq-eq-ℕ
  ; eq-Eq-ℕ)
_ : (m n : ℕ) → (m ＝ n) ↔ Eq-ℕ m n
_ = λ m n → (Eq-eq-ℕ , (eq-Eq-ℕ m n))
```

### 6.4 Peano's seventh and eighth axioms

**Theorem 6.4.1.** Peano's seventh axiom.

TODO: do we have `app succ-ℕ` as a definition?

```agda
open import elementary-number-theory.natural-numbers using
  ( is-injective-succ-ℕ)
_ : (m n : ℕ) → (m ＝ n) ↔ (succ-ℕ m ＝ succ-ℕ n)
_ = λ m n → (ap succ-ℕ , is-injective-succ-ℕ)
```

**Theorem 6.4.2.** Peano's eighth axiom.

```agda
open import elementary-number-theory.natural-numbers using
  ( is-nonzero-succ-ℕ)
```

The above proof uses Agda's built-in mechanism for recognizing that two elemens
of an inductive type built out of different constructors cannot be equal (the
"no confusion" principle). The proof from the book follows:

```agda
_ : (n : ℕ) → ¬ (zero-ℕ ＝ succ-ℕ n)
_ = λ n → Eq-eq-ℕ
```

### Exercises

**Exercise 6.1.** Addition and multiplication by a positive natural number are
injective functions.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( is-injective-right-add-ℕ)
_ : (m n k : ℕ) → (m ＝ n) ↔ (add-ℕ m k ＝ add-ℕ n k)
_ = λ m n k → (ap (λ x → add-ℕ x k) , is-injective-right-add-ℕ k)
open import elementary-number-theory.multiplication-natural-numbers using
  ( is-injective-right-mul-succ-ℕ)
_ : (m n k : ℕ) → (m ＝ n) ↔ (mul-ℕ m (succ-ℕ k) ＝ mul-ℕ n (succ-ℕ k))
_ =
  λ m n k → (ap (λ x → mul-ℕ x (succ-ℕ k)) , is-injective-right-mul-succ-ℕ k)
-- TODO: b, c, report that multiplication is denoted by juxtaposition
```

**Exercise 6.2.** Observational equality of booleans.

```agda
open import foundation.booleans using
  ( Eq-bool)
open import foundation.booleans using
  ( Eq-eq-bool
  ; eq-Eq-bool)
_ : (x y : bool) → (x ＝ y) ↔ Eq-bool x y
_ = λ x y → (Eq-eq-bool , eq-Eq-bool)
open import foundation.booleans using
  ( neq-neg-bool -- b ≠ neg-bool b
  )
```

**Exercise 6.3.** Standard linear order on ℕ.

```agda
open import elementary-number-theory.inequality-natural-numbers using
  ( _≤-ℕ_)
open import elementary-number-theory.inequality-natural-numbers using
  ( refl-leq-ℕ
  ; antisymmetric-leq-ℕ
  ; transitive-leq-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( linear-leq-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( preserves-leq-left-add-ℕ
  ; reflects-leq-left-add-ℕ)
_ : (m n k : ℕ) → (m ≤-ℕ n) ↔ (add-ℕ m k ≤-ℕ add-ℕ n k)
_ =
  λ m n k → (preserves-leq-left-add-ℕ k m n , reflects-leq-left-add-ℕ k m n)
open import elementary-number-theory.inequality-natural-numbers using
  ( preserves-leq-left-mul-ℕ
  ; reflects-order-mul-ℕ)
_ : (m n k : ℕ) → (m ≤-ℕ n) ↔ (mul-ℕ m (succ-ℕ k) ≤-ℕ mul-ℕ n (succ-ℕ k))
_ =
  λ m n k →
    (preserves-leq-left-mul-ℕ (succ-ℕ k) m n , reflects-order-mul-ℕ k m n)
open import elementary-number-theory.minimum-natural-numbers using
  ( is-greatest-lower-bound-min-ℕ)
open import elementary-number-theory.maximum-natural-numbers using
  ( is-least-upper-bound-max-ℕ)
```

**Exercise 6.4.** Standard strict order on ℕ.

```agda
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( _<-ℕ_)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( anti-reflexive-le-ℕ
  ; antisymmetric-le-ℕ
  ; transitive-le-ℕ)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( succ-le-ℕ -- n < n + 1
  ; preserves-le-succ-ℕ -- m < n → m < n + 1
  )
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( leq-succ-le-ℕ
  ; contradiction-le-ℕ)
-- TODO: backward directions
```

**Exercise 6.5.** Distance function on ℕ.

```agda
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-eq-ℕ
  ; eq-dist-ℕ
  ; symmetric-dist-ℕ -- dist m n = dist n m
  ; triangle-inequality-dist-ℕ -- dist m n ≤ dist m k + dist k n
  )
_ : (m n : ℕ) → (m ＝ n) ↔ (dist-ℕ m n ＝ zero-ℕ)
_ = λ m n → (dist-eq-ℕ m n , eq-dist-ℕ m n)
-- TODO: b
open import elementary-number-theory.distance-natural-numbers using
  ( translation-invariant-dist-ℕ -- dist (a + m) (a + n) = dist m n
  ; left-distributive-mul-dist-ℕ' -- dist (k * m) (k * n) = k * (dist m n)
  )
```

**Exercise 6.6.** The absolute value function.

```agda
open import elementary-number-theory.absolute-value-integers using
  ( abs-ℤ
  ; eq-abs-ℤ
  ; abs-eq-ℤ
  ; subadditive-abs-ℤ -- |x + y| < |x| + |y|
  ; multiplicative-abs-ℤ -- |x * y| = |x| * |y|
  )
_ : (x : ℤ) → (x ＝ zero-ℤ) ↔ (abs-ℤ x ＝ zero-ℕ)
_ = λ x → (abs-eq-ℤ x , eq-abs-ℤ x)
```

## 7 Modular arithmetic via the Curry-Howard interpretation

### 7.1 The Curry-Howard interpretation

**Definition 7.1.2.** The divisibility relation.

Note that the library's division relation uses the property `k * d = n`, as
opposed to the book's `d * k = n`.

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-ℕ)
```

**Example 7.1.4.** Divisibility by one.

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-one-ℕ)
```

**Proposition 7.1.5.** A 3-for-2 property of division.
<a id="proposition-7.1.5"></a>

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-add-ℕ)
```

The other other two claims are shown in Exercise [7.1](#exercise-7.1).

### 7.2 The congruence relations on ℕ

**Definition 7.2.1.** Typal binary relations.

```agda
open import foundation.binary-relations using
  ( Relation
  ; is-reflexive
  ; is-symmetric
  ; is-transitive)
-- TODO: there is no is-equivalence, and equivalence relations are only Prop-valued. Why?
```

**Definition 7.2.2.** Congruence relations on ℕ.

```agda
open import elementary-number-theory.congruence-natural-numbers using
  ( _≡_mod_)
```

**Example 7.2.3.** The modulus is congruent to zero.

```agda
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-zero-ℕ)
```

**Proposition 7.2.4.** Congruence modulo `k` is an equivalence relation.

```agda
open import elementary-number-theory.congruence-natural-numbers using
  ( refl-cong-ℕ
  ; symmetric-cong-ℕ
  ; transitive-cong-ℕ)
```

### 7.3 The standard finite types

**Definition 7.3.2.** The standard finite types.

TODO: is neg-one-Fin called that because it's "k - 1"?

TODO: we could implement the pattern matching on `i(x)` and `*` instead of
`inl x` and `inr *` by using pattern synonyms. Would we be interested in that?

```agda
open import univalent-combinatorics.standard-finite-types using
  ( Fin
  ; inl-Fin -- inclusion Fin k → Fin (k + 1)
  ; neg-one-Fin -- point Fin (k + 1)
  )
```

**Definition 7.3.4.** Inclusion into ℕ.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( nat-Fin)
```

**Lemma 7.3.5.** The inclusion into ℕ is bounded.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( strict-upper-bound-nat-Fin)
```

**Proposition 7.3.6.** The inclusion into ℕ is injective.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( is-injective-nat-Fin)
```

### 7.4 The natural numbers modulo `k + 1`

**Definition 7.4.1.** Split surjective functions.

```agda
open import foundation.split-surjective-maps using
  ( is-split-surjective)
```

**Definition 7.4.2.** Zero and successor on standard finite types.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( zero-Fin
  ; skip-zero-Fin
  ; succ-Fin)
```

**Definition 7.4.3.** The surjection from ℕ into standard finite types.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ -- [-]ₖ₊₁
  )
```

**Lemma 7.4.4.** Preservation of zero and successor `mod k`.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( is-zero-nat-zero-Fin -- ι(zero) = 0
  ; nat-skip-zero-Fin -- ι(skip-zero x) = ι(x) + 1
  )
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-nat-succ-Fin -- ι(succ x) ≡ ι(x) + 1 mod k
  )
```

**Proposition 7.4.5.**

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-nat-mod-succ-ℕ -- ι[x]ₖ₊₁ ≡ x mod (k + 1)
  )
```

**Proposition 7.4.6.**

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( is-zero-div-ℕ
  ; div-is-zero-ℕ)
_ : (d x : ℕ) → x <-ℕ d → div-ℕ d x ↔ (x ＝ 0)
_ = λ d x x<d → (is-zero-div-ℕ d x x<d , div-is-zero-ℕ d x)
open import elementary-number-theory.congruence-natural-numbers using
  ( eq-cong-le-dist-ℕ
  ; cong-identification-ℕ)
_ : (k x y : ℕ) → dist-ℕ x y <-ℕ k → x ≡ y mod k ↔ (x ＝ y)
_ = λ k x y dist<d → (eq-cong-le-dist-ℕ k x y dist<d , cong-identification-ℕ k)
```

**Theorem 7.4.7.** Equality modulo `k + 1` corresponds to equality after
inclusion to `Fin (k + 1)`.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-eq-mod-succ-ℕ
  ; eq-mod-succ-cong-ℕ)
_ : (k x y : ℕ) → (mod-succ-ℕ k x ＝ mod-succ-ℕ k y) ↔ (x ≡ y mod (succ-ℕ k))
_ = λ k x y → (cong-eq-mod-succ-ℕ k x y , eq-mod-succ-cong-ℕ k x y)
```

**Theorem 7.4.8.** The map from natural numbers is split surjective.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-split-surjective-mod-succ-ℕ)
```

### 7.5 The cyclic groups

**Definition 7.5.1.** The cyclic groups.

```agda
open import elementary-number-theory.modular-arithmetic using
  ( ℤ-Mod -- ℤ/k
  )
```

**Definition 7.5.2.** Addition on `ℤ/(k + 1)` and additive inverse.

```agda
open import elementary-number-theory.modular-arithmetic using
  ( add-ℤ-Mod
  ; neg-ℤ-Mod)
```

**Remark 7.5.3.**

The lemmas are proven for all natural numbers `k`, not just positive ones.

```agda
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-is-zero-nat-zero-Fin -- ι(0) ≡ 0 mod (k + 1)
  )
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-add-Fin -- ι(x + y) ≡ ι(x) + ι(y) mod (k + 1)
  ; cong-neg-Fin -- ι(-x) ≡ dist(ι(x), k + 1) mod (k + 1)
  )
```

**Proposition 7.5.4.** A 3-for-2 property of congruences.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( congruence-add-ℕ
  ; cong-right-summand-ℕ
  ; cong-left-summand-ℕ)
```

**Theorem 7.5.5.** ℤ/k with addition and negation form an Abelian group.

```agda
open import elementary-number-theory.modular-arithmetic using
  ( left-unit-law-add-ℤ-Mod -- 0 + x = x
  ; right-unit-law-add-ℤ-Mod -- x + 0 = x
  ; left-inverse-law-add-ℤ-Mod -- (-x) + x = 0
  ; right-inverse-law-add-ℤ-Mod -- x + (-x) = 0
  ; associative-add-ℤ-Mod -- (x + y) + z = x + (y + z)
  ; commutative-add-ℤ-Mod -- x + y = y + x
  )
```

### Exercises

**Exercise 7.1.** The rest of Proposition [7.1.5](#proposition-7.1.5)
<a id="exercise-7.1"></a>

**Exercise 7.2.** Divisibility is a partial order.

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( refl-div-ℕ
  ; antisymmetric-div-ℕ
  ; transitive-div-ℕ)
```

**Exercise 7.3.** `n!` is divisible by all `0 < x ≤ n`

```agda
open import elementary-number-theory.factorials using
  ( div-factorial-ℕ)
```

**Exercise 7.4.** The successor on `Fin (k + 1)` adds one.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-add-one-succ-Fin')
```

**Exercise 7.5.** Observational equality of `Fin k`.

```agda
open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin-eq
  ; eq-Eq-Fin)
_ : (k : ℕ) → {x y : Fin k} → (x ＝ y) ↔ Eq-Fin k x y
_ = λ k → (Eq-Fin-eq k , eq-Eq-Fin k)
open import univalent-combinatorics.standard-finite-types using
  ( is-injective-inl-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( neq-zero-succ-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( is-injective-succ-Fin)
```

**Exercise 7.6.** The predecessor function on `Fin k`.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( neg-two-Fin
  ; skip-neg-two-Fin
  ; pred-Fin
  ; is-section-pred-Fin -- succ (pred x) = x
  ; is-retraction-pred-Fin -- pred (succ x) = x
  )
```

**Exercise 7.7.** Classical finite types.

```agda
open import univalent-combinatorics.classical-finite-types using
  ( classical-Fin)
open import univalent-combinatorics.classical-finite-types using
  ( Eq-classical-Fin
  ; Eq-eq-classical-Fin
  ; eq-Eq-classical-Fin)
_ : (k : ℕ) → (x y : classical-Fin k) → (x ＝ y) ↔ Eq-classical-Fin k x y
_ = λ k x y → (Eq-eq-classical-Fin k x y , eq-Eq-classical-Fin k x y)
open import univalent-combinatorics.classical-finite-types using
  ( classical-standard-Fin -- ι
  ; standard-classical-Fin -- α
  ; is-section-classical-standard-Fin -- α (ι x) = x
  ; is-retraction-classical-standard-Fin -- ι (α y) = y
  )
```

**Exercise 7.8.** Multiplication on `ℤ/(k + 1)`.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mul-Fin)
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-mul-Fin -- ι(x * y) ≡ ι x * ι y mod (k + 1)
  )
open import elementary-number-theory.congruence-natural-numbers using
  ( congruence-mul-ℕ -- x ≡ x' → y ≡ y' → (x * y) ≡ (x' * y')
  )
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( associative-mul-Fin -- (x * y) * z = x * (y * z)
  ; commutative-mul-Fin -- x * y = y * x
  ; left-unit-law-mul-Fin -- 1 * x = x
  ; right-unit-law-mul-Fin -- x * 1 = x
  ; left-distributive-mul-add-Fin -- x * (y + z) = x * y + x * z
  ; right-distributive-mul-add-Fin -- (x + y) * z = x * z + y * z
  )
```

**Exercise 7.9.** Euclidean division.

```agda
open import elementary-number-theory.euclidean-division-natural-numbers using
  ( euclidean-division-ℕ)
-- TODO: b
```

**Exercise 7.10.** `k`-ary natural numbers.

```agda
open import elementary-number-theory.finitary-natural-numbers using
  ( based-ℕ -- ℕₖ
  ; convert-based-ℕ -- fₖ
  )
open import elementary-number-theory.finitary-natural-numbers using
  ( is-empty-based-zero-ℕ)
open import elementary-number-theory.finitary-natural-numbers using
  ( is-injective-convert-based-ℕ)
open import elementary-number-theory.finitary-natural-numbers using
  ( inv-convert-based-ℕ -- gₖ
  ; is-section-inv-convert-based-ℕ -- fₖ₊₁ (gₖ n) = n
  ; is-retraction-inv-convert-based-ℕ -- gₖ (fₖ₊₁ x) = x
  )
```

## 8 Decidability in elementary number theory

### 8.1 Decidability and decidable equality

**Definition 8.1.1.** Decidable types.

```agda
open import foundation.decidable-types using
  ( is-decidable)
```

**Example 8.1.2.** The unit type and the empty type are decidable

```agda
open import foundation.decidable-types using
  ( is-decidable-unit
  ; is-decidable-empty)
```

**Example 8.1.3.** Decidability of coproducts, products and functions.

```agda
open import foundation.decidable-types using
  ( is-decidable-coproduct -- if A and B are decidable, then A + B is decidable
  ; is-decidable-product -- if A and B are decidable, then A × B is decidable
  ; is-decidable-function-type -- if A and B are decidable, then A → B is decidable
  ; is-decidable-neg -- if A is decidable, then ¬A is decidable
  )
```

**Example 8.1.4.** Decidability of observational equality and inequality on ℕ.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( is-decidable-Eq-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( is-decidable-leq-ℕ)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( is-decidable-le-ℕ)
```

**Definition 8.1.5.** Decidable equality.

```agda
open import foundation.decidable-equality using
  ( has-decidable-equality)
```

**Lemma 8.1.6.** Decidability of logically equivalent types is logically
equivalent.

```agda
open import foundation.decidable-types using
  ( is-decidable-iff')
```

**Proposition 8.1.7.** Equality on ℕ is decidable.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ)
```

**Proposition 8.1.8.** Equality on `Fin k` is decidable.

```agda
open import univalent-combinatorics.equality-standard-finite-types using
  ( is-decidable-Eq-Fin
  ; has-decidable-equality-Fin)
```

**Theorem 8.1.9.** Divisibility is decidable.

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( is-decidable-div-ℕ)
```

### 8.2 Constructions by case analysis

**Definition 8.2.1.** The Collatz function. TODO: report that "collatz function"
is inconsistently capitalized.

Note that we don't store the helper function `h` in a separate definition.
Instead we use Agda's `with` abstraction to do case analysis on the result of
`is-decidable-div-ℕ 2 n`, as explained in Remark 8.2.2.

```agda
open import elementary-number-theory.collatz-conjecture using
  ( collatz)
```

**Proposition 8.2.3.** Decidability of products and function types with weaker
assumptions.

```agda
open import foundation.decidable-types using
  ( is-decidable-product'
  ; is-decidable-function-type')
```

**Proposition 8.2.4.**

```agda
open import elementary-number-theory.decidable-types using
  ( is-decidable-Π-ℕ)
```

**Corollary 8.2.5.** TODO: "upper bound for P" is only defined in the next
section.

```agda
open import elementary-number-theory.decidable-types using
  ( is-decidable-bounded-Π-ℕ)
```

### 8.3 The well-ordering principle of ℕ

**Definition 8.3.1.** Bounds for families over ℕ.

```agda
open import elementary-number-theory.lower-bounds-natural-numbers using
  ( is-lower-bound-ℕ)
open import elementary-number-theory.upper-bounds-natural-numbers using
  ( is-upper-bound-ℕ)
open import elementary-number-theory.well-ordering-principle-natural-numbers using
  ( minimal-element-ℕ)
```

**Theorem 8.3.2.** Well-ordering principle of ℕ.

```agda
open import elementary-number-theory.well-ordering-principle-natural-numbers using
  ( well-ordering-principle-ℕ)
```

### 8.4 The greatest common divisor

**Definition 8.4.1.** The type of greatest common divisors.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( is-gcd-ℕ)
```

**Proposition 8.4.2.** Uniqueness of the greatest common divisor.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( uniqueness-is-gcd-ℕ)
```

**Definition 8.4.3.** Multiples of the greatest common divisor.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( is-multiple-of-gcd-ℕ)
```

**Proposition 8.4.4.** Decidability of multiples of the greatest common divisor.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( is-decidable-is-multiple-of-gcd-ℕ)
```

**Lemma 8.4.5.** `a + b` is a multiple of `gcd(a, b)`.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( sum-is-multiple-of-gcd-ℕ)
```

**Definition 8.4.6.** The greatest common divisor.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( gcd-ℕ)
```

**Lemma 8.4.7.** `gcd(a, b)` is zero if and only if `a + b` = 0.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( is-zero-gcd-ℕ
  ; is-zero-add-is-zero-gcd-ℕ)
_ : (a b : ℕ) → (gcd-ℕ a b ＝ zero-ℕ) ↔ (add-ℕ a b ＝ zero-ℕ)
_ = λ a b → (is-zero-add-is-zero-gcd-ℕ a b , is-zero-gcd-ℕ a b)
```

**Theorem 8.4.8.** `gcd(a, b)` is a greatest common divisor.

```agda
open import elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( is-gcd-gcd-ℕ)
```

### 8.5 The infinitude of primes

**Definition 8.5.1.** Proper divisors and primes.

```agda
open import elementary-number-theory.proper-divisors-natural-numbers using
  ( is-proper-divisor-ℕ)
open import elementary-number-theory.prime-numbers using
  ( is-prime-ℕ)
```

**Proposition 8.5.2.** Being a prime is decidable.

```agda
open import elementary-number-theory.prime-numbers using
  ( is-decidable-is-prime-ℕ)
```

**Definition 8.5.3.** Sieve of Erathostenes.

```agda
open import elementary-number-theory.sieve-of-eratosthenes using
  ( in-sieve-of-eratosthenes-ℕ)
```

**Lemma 8.5.4.** Being in the sieve of Erathostenes is decidable.

```agda
open import elementary-number-theory.sieve-of-eratosthenes using
  ( is-decidable-in-sieve-of-eratosthenes-ℕ)
```

**Lemma 8.5.5.** `n! + 1` is above `n` in the sieve.

```agda
open import elementary-number-theory.sieve-of-eratosthenes using
  ( in-sieve-of-eratosthenes-succ-factorial-ℕ)
```

**Theorem 8.5.6.** Infinitude of primes.

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( infinitude-of-primes-ℕ)
```

### 8.6 Boolean reflection

**Definition 8.6.1.** Booleanization.

```agda
open import reflection.boolean-reflection using
  ( booleanization)
```

**Theorem 8.6.2.** Boolean reflection principle.

```agda
open import reflection.boolean-reflection using
  ( boolean-reflection -- reflect
  )
_ : is-prime-ℕ 37
_ = boolean-reflection (is-decidable-is-prime-ℕ 37) refl
```

### Exercises

**Exercise 8.1.** Statements of famous conjectures.

```agda
open import elementary-number-theory.goldbach-conjecture using
  ( Goldbach-conjecture)
open import elementary-number-theory.twin-prime-conjecture using
  ( twin-prime-conjecture)
open import elementary-number-theory.collatz-conjecture using
  ( Collatz-conjecture)
```

**Exercise 8.2.** `is-decidable` is idempotent.

```agda
open import foundation.decidable-types using
  ( idempotent-is-decidable -- is-decidable (is-decidable P) → is-decidable P
  )
```

**Exercise 8.3.** Markov's principle over finite types.

```agda
open import elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( exists-not-not-for-all-Fin -- ¬((x : Fin k) → P x) → Σ (x : Fin k) ¬(P x)
  )
```

**Exercise 8.4.** Prime functions.

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( prime-ℕ -- n-th prime
  ; prime-counting-ℕ -- number of primes less than or equal `n`
  )
```

**Exercise 8.5.** Alternative definition of prime numbers.

TODO

**Exercise 8.6.** Products have decidable equality if and only if factors have
decidable equality, assuming the other factor is pointed.

```agda
open import foundation.decidable-equality using
  ( has-decidable-equality-product'
  ; has-decidable-equality-left-factor
  ; has-decidable-equality-right-factor)
_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (B → has-decidable-equality A) × (A → has-decidable-equality B) ↔
  has-decidable-equality (A × B)
_ =
  ( λ (eqA , eqB) → has-decidable-equality-product' eqA eqB) ,
  ( λ eqAB →
    has-decidable-equality-left-factor eqAB ,
    has-decidable-equality-right-factor eqAB)
open import foundation.decidable-equality using
  ( has-decidable-equality-product)
```

**Exercise 8.7.** Observational equality of coproducts.

TODO: Equality of coproducts is defined as an inductive instead of recursively.
Is that because the identity types need to be raised?

```agda
open import foundation.equality-coproduct-types using
  ( Eq-coproduct)
open import foundation.equality-coproduct-types using
  ( Eq-eq-coproduct
  ; eq-Eq-coproduct)
_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (x y : A + B) → (x ＝ y) ↔ Eq-coproduct x y
_ = λ x y → (Eq-eq-coproduct x y , eq-Eq-coproduct x y)
open import foundation.decidable-equality using
  ( has-decidable-equality-coproduct
  ; has-decidable-equality-left-summand
  ; has-decidable-equality-right-summand)
_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A × has-decidable-equality B ↔
  has-decidable-equality (A + B)
_ =
  ( λ (eqA , eqB) → has-decidable-equality-coproduct eqA eqB) ,
  ( λ eqAB →
    has-decidable-equality-left-summand eqAB ,
    has-decidable-equality-right-summand eqAB)
open import elementary-number-theory.equality-integers using
  ( has-decidable-equality-ℤ)
```

**Exercise 8.8.** Decidable equality in dependent pair types.

TODO: This needs Eq-Σ, which is introduced in Section 9.3, right?

```agda
open import foundation.decidable-equality using
  ( has-decidable-equality-Σ
  ; has-decidable-equality-fiber-has-decidable-equality-Σ)
_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → has-decidable-equality A →
  ((x : A) → has-decidable-equality (B x)) ↔
  has-decidable-equality (Σ A B)
_ =
  λ eqA →
    has-decidable-equality-Σ eqA ,
    has-decidable-equality-fiber-has-decidable-equality-Σ eqA
open import foundation.decidable-equality using
  ( has-decidable-equality-base-has-decidable-equality-Σ)
```

**Exercise 8.9.** Decidability and decidable equality of dependent function out
of `Fin k`

TODO: Decidable equality needs function extensionality, right?

```agda
open import univalent-combinatorics.decidable-dependent-function-types using
  ( is-decidable-Π-Fin)
-- TODO: b
```

**Exercise 8.10.** Definition of the greatest common divisor as the maximal
element of common divisors.

TODO

**Exercise 8.11.** Bézout's identity.

```agda
open import elementary-number-theory.bezouts-lemma-natural-numbers using
  ( is-decidable-is-distance-between-multiples-ℕ
    --^ Σ (k : ℕ) Σ (l : ℕ) dist(k*x, l*x) = z is decidable
  ; minimal-positive-distance-x-coeff
  ; minimal-positive-distance-y-coeff
  ; bezouts-lemma-eqn-ℕ
  )
-- TODO: handle a+b=0
_ :
  (x y : ℕ) → ¬ (add-ℕ x y ＝ zero-ℕ) →
  Σ ℕ (λ k → Σ ℕ (λ l → dist-ℕ (mul-ℕ k x) (mul-ℕ l y) ＝ gcd-ℕ x y))
_ =
  λ x y possum →
    minimal-positive-distance-x-coeff x y possum ,
    minimal-positive-distance-y-coeff x y possum ,
    bezouts-lemma-eqn-ℕ x y possum
```

**Exercise 8.12.** Prime factor decomposition.

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( nat-least-nontrivial-divisor-ℕ -- for every 1 < n a number...
  ; is-prime-least-nontrivial-divisor-ℕ -- which is a prime...
  ; div-least-nontrivial-divisor-ℕ -- and divides n
  )
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( list-fundamental-theorem-arithmetic-ℕ -- for every 1 < n a list of numbers...
  ; is-sorted-list-fundamental-theorem-arithmetic-ℕ -- which is sorted...
  ; is-prime-list-fundamental-theorem-arithmetic-ℕ -- only contains primes...
  ; is-decomposition-list-fundamental-theorem-arithmetic-ℕ -- and multiplies up to n
  )
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( eq-prime-decomposition-list-ℕ -- prime decompositions of a fixed number are equal
  )
```

**Exercise 8.13.** TODO

**Exercise 8.14.** Prime fields.

TODO.

**Exercise 8.15.** The cofibonacci sequenece.

```agda
open import elementary-number-theory.cofibonacci using
  ( cofibonacci
  ; forward-is-left-adjoint-cofibonacci)
-- TODO: backward direction of the adjointness equivalence
```
