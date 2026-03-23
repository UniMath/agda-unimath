# Introduction to homotopy type theory

This file collects references to formalization of constructions, propositions,
theorems and exercises from Rijke's Introduction to Homotopy Type Theory
{{#cite Rij22}}.

```agda
module literature.introduction-to-homotopy-type-theory where

open import foundation.universe-levels
```

The first two sections introduce the metatheory of dependent type theories,
which corresponds to built-in features of Agda.

## 2 Dependent function types

### 2.2 Ordinary function types

**Definition 2.2.3.** The identity function.

```agda
open import foundation.function-types using
  ( id)
```

**Definition 2.2.5.** Function composition.

```agda
open import foundation.function-types using
  ( _∘_ -- comp
  )
```

**Lemma 2.2.6.** Function composition is associative.

```agda
open import foundation.function-types using
  ( associative-comp)
```

### Exercises

**Exercise 2.3.** The constant map.

```agda
open import foundation.constant-maps using
  ( const)
```

**Exercise 2.4.** The swap function.

```agda
open import foundation.type-arithmetic-dependent-function-types using
  ( swap-Π)
```

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

**Definition 3.2.1.** Addition on the natural numbers.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ ; _+ℕ_)
```

### 3.3 Pattern matching

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( Fibonacci-ℕ)
```

### Exercises

**Exercise 3.1.** Multiplication and exponentiation.

```agda
-- (a)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ ; _*ℕ_)

-- (b)
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
-- (a)
open import elementary-number-theory.triangular-numbers using
  ( triangular-number-ℕ)

-- (b)
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

```agda
div-two-pattern-match : ℕ → ℕ
div-two-pattern-match 0 = 0
div-two-pattern-match 1 = 0
div-two-pattern-match (succ-ℕ (succ-ℕ n)) = succ-ℕ (div-two-pattern-match n)
```

For the definition using the induction principle, we think of iterating the
swapping operation `(m, 0) ↦ (m, 1) ; (m, 1) ↦ (m + 1, 0)`, using the same
encoding of pairs with functions as the definition of the Fibonacci sequence.

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( shift-one ; shift-two)

div-two-induction-step : (ℕ → ℕ) → (ℕ → ℕ)
div-two-induction-step f =
  ind-ℕ
    ( shift-one (f 0) (λ _ → 1))
    ( λ _ _ → shift-one (succ-ℕ (f 0)) (λ _ → 0))
    ( f 1)

div-two-induction-zero : ℕ → ℕ
div-two-induction-zero = λ _ → 0

div-two-induction-function : ℕ → (ℕ → ℕ)
div-two-induction-function =
  ind-ℕ
    ( div-two-induction-zero)
    ( λ _ → div-two-induction-step)

div-two-induction : ℕ → ℕ
div-two-induction n = div-two-induction-function n 0
```

## 4 More inductive types

### 4.2 The unit type

**Definition 4.2.1.** The unit type.

Note that the unit type in the library is defined as a _record_ type, as opposed
to an inductive type with one constructor. That allows us to have a judmental
eta law, which states that every element of the unit type is judgmentally equal
to `star`. This rule is not assumed in the book.

```agda
open import foundation.unit-type using
  ( unit -- 𝟏
  ; star -- ⋆
  ; ind-unit
  ; point -- pt
  )
```

### 4.3 The empty type

**Definition 4.3.1.** The empty type.

```agda
open import foundation.empty-types using
  ( empty -- ∅
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
  ; ind-coproduct -- [f, g]
  ; rec-coproduct)
```

**Remark 4.4.2.** Coproducts of functions.

```agda
open import foundation.functoriality-coproduct-types using
  ( map-coproduct -- f + g : A + B → A' + B'
  )
```

**Proposition 4.4.3.** Projections from coproducts with an empty type.

```agda
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coproduct-is-empty -- is-empty B → (A + B) → A
  )
```

### 4.5 The type of integers

**Definition 4.5.1.** The integers.

```agda
open import elementary-number-theory.integers using
  ( ℤ
  ; in-pos-ℤ
  ; in-neg-ℤ
  ; neg-one-ℤ -- -1
  ; zero-ℤ -- 0
  ; one-ℤ -- 1
  )
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

Note that similarly to the unit type, dependent pair types are defined as a
record and enjoy a judgmental eta law in the library.

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
-- (a)
open import elementary-number-theory.integers using
  ( pred-ℤ)

-- (b)
open import elementary-number-theory.addition-integers using
  ( add-ℤ)
open import elementary-number-theory.integers using
  ( neg-ℤ)

-- (c)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ)
```

**Exercise 4.2.** Boolean negation, conjunction and disjunction.

```agda
open import foundation.booleans using
  ( bool
  ; false
  ; true
  ; ind-bool)

-- (a)
open import foundation.logical-operations-booleans using
  ( neg-bool)

-- (b)
open import foundation.logical-operations-booleans using
  ( and-bool)

-- (c)
open import foundation.logical-operations-booleans using
  ( or-bool)
```

**Exercise 4.3.** Double negation.

Note that we call bi-implications _logical equivalences_ in the library.

A type `X` for which we can show `¬¬X` is called _irrefutable_.

```agda
open import foundation.logical-equivalences using
  ( _↔_)

-- (a)
_ : {l : Level} (P : UU l) → ¬ (P × ¬ P)
_ = λ P (p , np) → np p
open import foundation.negation using
  ( no-fixed-points-neg -- ¬(P ↔ ¬P)
  )

-- (b)
open import foundation.double-negation using
  ( ¬¬_
  ; intro-double-negation -- P → ¬¬P
  ; map-double-negation -- (P → Q) → (¬¬P → ¬¬Q)
  ; extend-double-negation -- (P → ¬¬Q) → (¬¬P → ¬¬Q)
  )

-- (c)
open import foundation.double-negation using
  ( double-negation-double-negation-elim -- ¬¬(¬¬P → P)
  ; double-negation-Peirces-law -- ¬¬(((P → Q) → P) → P)
  ; double-negation-linearity-implication -- ¬¬((P → Q) + (Q → P))
  )
open import logic.irrefutable-types using
  ( is-irrefutable-is-decidable -- ¬¬(P + ¬P)
  )

-- (d)
open import foundation.decidable-types using
  ( double-negation-elim-is-decidable -- (P + ¬P) → (¬¬P → P)
  )

_ : {l1 l2 : Level} (P : UU l1) (Q : UU l2) → ¬¬ (Q → P) → ((P + ¬ P) → Q → P)
_ =
  λ P Q nnqp →
    rec-coproduct (λ p q → p) (λ np q → ex-falso (nnqp (λ qp → np (qp q))))

_ : {l1 l2 : Level} (P : UU l1) (Q : UU l2) → ((P + ¬ P) → Q → P) → ¬¬ (Q → P)
_ =
  λ P Q pnpqp nqp →
    ( λ (np : ¬ P) → nqp (pnpqp (inr np)))
    ( λ (p : P) → nqp (λ _ → p))

-- (e)
open import logic.double-negation-elimination using
  ( double-negation-elim-neg -- ¬¬(¬ P) → P
  ; double-negation-elim-exp-neg-neg -- ¬¬(P → ¬¬Q) → (P → ¬¬Q)
  ; double-negation-elim-product
  )

_ :
  {l1 l2 : Level} (P : UU l1) (Q : UU l2) →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
_ =
  λ P Q →
    double-negation-elim-product
      ( double-negation-elim-neg (¬ P))
      ( double-negation-elim-neg (¬ Q))

-- (f)
open import logic.irrefutable-types using
  ( is-irrefutable-product -- ¬¬A → ¬¬B → ¬¬(A × B)
  )

module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where
  _ : ¬¬ (P × Q) → ¬¬ P × ¬¬ Q
  _ =
    λ nnpq → (λ np → nnpq (λ (p , q) → np p)) , (λ nq → nnpq (λ (p , q) → nq q))

  _ : ¬¬ (P + Q) → ¬ (¬ P × ¬ Q)
  _ =
    λ nnpq (np , nq) → nnpq (rec-coproduct np nq)
  _ : ¬ (¬ P × ¬ Q) → ¬¬ (P + Q)
  _ = λ nnpnq npq → nnpnq ((λ p → npq (inl p)) , (λ q → npq (inr q)))

  _ : ¬¬ (P → Q) → (¬¬ P → ¬¬ Q)
  _ = λ nnpq nnp nq → nnp (λ p → nnpq (λ pq → nq (pq p)))

  _ : (¬¬ P → ¬¬ Q) → ¬¬ (P → Q)
  _ =
    λ nnpnnq npq →
      ( λ (nq : ¬ Q) →
        npq (λ p → ex-falso (nnpnnq (intro-double-negation p) nq)))
      ( λ (q : Q) → npq (λ _ → q))
```

**Exercise 4.4.** Lists.

```agda
open import lists.lists using
  ( list
  ; nil
  ; cons)

-- (a)
open import lists.lists using
  ( ind-list)

-- (b)
open import lists.lists using
  ( fold-list)

-- (c)
open import lists.functoriality-lists using
  ( map-list)

-- (d)
open import lists.lists using
  ( length-list)

-- (e)
open import elementary-number-theory.sums-of-finite-sequences-of-natural-numbers using
  ( sum-list-ℕ)
open import elementary-number-theory.products-of-natural-numbers using
  ( product-list-ℕ)

-- (f)
open import lists.concatenation-lists using
  ( concat-list)

-- (g)
open import lists.flattening-lists using
  ( flatten-list)

-- (h)
open import lists.reversing-lists using
  ( reverse-list)
```

## 5 Identity types

### 5.1 The inductive definition of identity types

**Definition 5.1.1.** The identity type.

```agda
open import foundation.identity-types using
  ( _＝_ ; Id
  ; refl
  ; ind-Id)
```

### 5.2 The groupoidal structure of types

**Definition 5.2.1.** Concatenation of identifications.

```agda
open import foundation.identity-types using
  ( concat ; _∙_)
```

**Definition 5.2.2.** Inverse operation.

```agda
open import foundation.identity-types using
  ( inv)
```

**Definition 5.2.4.** Associator.

```agda
open import foundation.identity-types using
  ( assoc -- (p ∙ q) ∙ r = p ∙ (q ∙ r)
  )
```

**Definition 5.2.5.** Unit law operations.

```agda
open import foundation.identity-types using
  ( left-unit -- refl ∙ p = p
  ; right-unit -- p ∙ refl = p
  )
```

**Definition 5.2.5.** Inverse law operations.

```agda
open import foundation.identity-types using
  ( left-inv -- inv p ∙ p = refl
  ; right-inv -- p ∙ inv p = refl
  )
```

### 5.3 The action on identifications of functions

**Definition 5.3.1.** Action on paths.

Note that the operations `ap-id` and `ap-comp` provide identifications in the
inverse direction from the ones in the book.

```agda
open import foundation.action-on-identifications-functions using
  ( ap
  ; ap-id -- ap id p = p
  ; ap-comp -- ap (g ∘ f) p = ap g (ap f (p))
  )
```

**Definition 5.3.2.** Preservation rules.

```agda
open import foundation.action-on-identifications-functions using
  ( ap-refl -- ap f refl = refl
  ; ap-inv -- ap f (inv p) = inv (ap f p)
  ; ap-concat -- ap f (p ∙ q) = ap f p ∙ ap f q
  )
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

**Proposition 5.5.1.** Contractibility of singletons.

```agda
open import foundation.torsorial-type-families using
  ( is-torsorial-Id)
open import foundation.contractible-types using
  ( eq-is-contr')

_ : {l : Level} {A : UU l} (a : A) (y : Σ A (λ x → a ＝ x)) → (a , refl) ＝ y
_ = λ a → eq-is-contr' (is-torsorial-Id a) (a , refl)
```

### 5.6 The laws of addition on ℕ

**Proposition 5.6.1.** Unit laws.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( left-unit-law-add-ℕ -- 0 + n = n
  ; right-unit-law-add-ℕ -- n + 0 = n
  )
```

**Proposition 5.6.2.** Successor laws.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( left-successor-law-add-ℕ -- succ m + n = succ (m + n)
  ; right-successor-law-add-ℕ -- m + succ n = succ (m + n)
  )
```

**Proposition 5.6.3.** Associativity.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( associative-add-ℕ -- (m + n) + k = m + (n + k)
  )
```

**Proposition 5.6.4.** Commutativity.

```agda
open import elementary-number-theory.addition-natural-numbers using
  ( commutative-add-ℕ -- m + n = n + m
  )
```

### Exercises

**Exercise 5.1.** Distributivity of inversion over concatenation.

```agda
open import foundation.identity-types using
  ( distributive-inv-concat -- inv (p ∙ q) = inv q ∙ inv p
  )
```

**Exercise 5.2.** Transposing concatenation.

```agda
open import foundation.identity-types using
  ( left-transpose-eq-concat -- (p ∙ q = r) → (q = inv p ∙ r)
  ; right-transpose-eq-concat -- (p ∙ q = r) → (p = r ∙ inv q)
  )
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
-- (a)
open import elementary-number-theory.multiplication-natural-numbers using
  ( right-zero-law-mul-ℕ -- m * 0 = 0
  ; left-zero-law-mul-ℕ -- 0 * m = 0
  ; right-unit-law-mul-ℕ -- m * 1 = m
  ; left-unit-law-mul-ℕ -- 1 * m = m
  ; right-successor-law-mul-ℕ -- m * (succ n) = m + m * n
  ; left-successor-law-mul-ℕ -- (succ m) * n = m * n + n
  )

-- (b)
open import elementary-number-theory.multiplication-natural-numbers using
  ( commutative-mul-ℕ -- m * n = n * m
  )

-- (c)
open import elementary-number-theory.multiplication-natural-numbers using
  ( left-distributive-mul-add-ℕ -- m * (n + k) = m * n + m * k
  ; right-distributive-mul-add-ℕ -- (m + n) * k = m * k + n * k
  )

-- (d)
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
-- (a)
open import elementary-number-theory.addition-integers using
  ( left-unit-law-add-ℤ -- 0 + x = x
  ; right-unit-law-add-ℤ -- x + 0 = x
  )

-- (b)
open import elementary-number-theory.addition-integers using
  ( left-predecessor-law-add-ℤ -- pred x + y = pred (x + y)
  ; right-predecessor-law-add-ℤ -- x + pred y = pred (x + y)
  ; left-successor-law-add-ℤ -- succ x + y = succ (x + y)
  ; right-successor-law-add-ℤ -- x + succ y = succ (x + y)
  )

-- (c)
open import elementary-number-theory.addition-integers using
  ( associative-add-ℤ -- (x + y) + z = x + (y + z)
  ; commutative-add-ℤ -- x + y = y + x
  )

-- (d)
open import elementary-number-theory.addition-integers using
  ( left-inverse-law-add-ℤ -- (-x) + x = 0
  ; right-inverse-law-add-ℤ -- x + (-x) = 0
  )
```

**Exercise 5.8.** Ring laws for multiplication of integers.

```agda
-- (a)
open import elementary-number-theory.multiplication-integers using
  ( left-zero-law-mul-ℤ -- 0 * x = x
  ; right-zero-law-mul-ℤ -- x * 0 = x
  ; left-unit-law-mul-ℤ -- 1 * x = x
  ; right-unit-law-mul-ℤ -- x * 1 = x
  )

-- (b)
open import elementary-number-theory.multiplication-integers using
  ( left-predecessor-law-mul-ℤ' -- pred x * y = x * y - y
  ; right-predecessor-law-mul-ℤ' -- x * pred y = x * y - x
  ; left-successor-law-mul-ℤ' -- succ x * y = x * y + y
  ; right-successor-law-mul-ℤ' -- x * succ y = x * y + x
  )

-- (c)
open import elementary-number-theory.multiplication-integers using
  ( left-distributive-mul-add-ℤ -- x * (y + z) = x * y + x * z
  ; right-distributive-mul-add-ℤ -- (x + y) * z = x * z + y * z
  )

-- (d)
open import elementary-number-theory.multiplication-integers using
  ( associative-mul-ℤ -- (x * y) * z = x * (y * z)
  ; commutative-mul-ℤ -- x * y = y * x
  )
```

## 6 Universes

### 6.1 Specification of type theoretic universes

**Definition 6.1.1** Universes.

The book's metatheory uses universes _à la Tarski_, which considers a universe
`𝒰` a type of _codes_, such that for every code `X : 𝒰` we may derive
`𝒯(X) type`. In contrast, Agda uses universes _à la Russell_, where the elements
`X : 𝒰` are themselves types.

The only exception is the universe types themselves — we have the type `Level`
of codes for universes, and for every code `l : Level` we have the judgment
`UU l type`.

Universes are called `UU` in the library, which stands for _univalent universe_.

Closure of universes under various type constructors is guaranteed by Agda's
[sort system](https://agda.readthedocs.io/en/latest/language/sort-system.html).

```agda
open import foundation.universe-levels using
  ( Level -- type of codes for universes
  ; UU -- the universal family decoding universes
  )
```

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

**Remark 6.2.4.** Inclusions into the successor universe.

```agda
open import foundation.raising-universe-levels using
  ( raise)

_ : (l : Level) → UU l → UU (lsuc l)
_ = λ l → raise (lsuc l)
```

**Definition 6.2.5.** The join of two universes.

```agda
open import foundation.universe-levels using
  ( _⊔_)
```

**Remark 6.2.6.** Universe arithmetic.

Note that while in the book `(𝒰 ⊔ 𝒱) ⊔ 𝒲` and `𝒰 ⊔ (𝒱 ⊔ 𝒲)` are a priori
unrelated, Agda considers them equal. Other universe equalities may be found in
[the documentation](https://agda.readthedocs.io/en/latest/language/universe-levels.html#intrinsic-level-properties).

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

```agda
open import elementary-number-theory.natural-numbers using
  ( is-injective-succ-ℕ)

_ : (m n : ℕ) → (m ＝ n) ↔ (succ-ℕ m ＝ succ-ℕ n)
_ = λ m n → (ap succ-ℕ , is-injective-succ-ℕ)
```

**Theorem 6.4.2.** Peano's eighth axiom.

```agda
open import elementary-number-theory.natural-numbers using
  ( is-nonzero-succ-ℕ -- succ n ≠ 0
  )
```

The above proof uses Agda's built-in mechanism for recognizing that two elements
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
-- (a)
open import elementary-number-theory.addition-natural-numbers using
  ( is-injective-right-add-ℕ)

_ : (m n k : ℕ) → (m ＝ n) ↔ (m +ℕ k ＝ n +ℕ k)
_ = λ m n k → (ap (λ x → x +ℕ k) , is-injective-right-add-ℕ k)

open import elementary-number-theory.multiplication-natural-numbers using
  ( is-injective-right-mul-succ-ℕ)

_ : (m n k : ℕ) → (m ＝ n) ↔ (m *ℕ (succ-ℕ k) ＝ n *ℕ (succ-ℕ k))
_ =
  λ m n k → (ap (λ x → x *ℕ (succ-ℕ k)) , is-injective-right-mul-succ-ℕ k)

open import elementary-number-theory.addition-natural-numbers using
  ( is-zero-summand-is-zero-sum-ℕ
  ; is-zero-sum-is-zero-summand-ℕ)

_ : (m n : ℕ) → (m +ℕ n ＝ 0) ↔ (m ＝ 0) × (n ＝ 0)
_ =
  λ m n →
    ( is-zero-summand-is-zero-sum-ℕ m n , is-zero-sum-is-zero-summand-ℕ m n)

open import elementary-number-theory.multiplication-natural-numbers using
  ( is-zero-summand-is-zero-mul-ℕ
  ; is-zero-mul-ℕ-is-zero-summand
  ; is-one-mul-ℕ
  ; is-one-left-is-one-mul-ℕ
  ; is-one-right-is-one-mul-ℕ)

_ : (m n : ℕ) → (m *ℕ n ＝ 0) ↔ (m ＝ 0) + (n ＝ 0)
_ =
  λ m n →
    is-zero-summand-is-zero-mul-ℕ m n , is-zero-mul-ℕ-is-zero-summand m n

_ : (m n : ℕ) → (m *ℕ n ＝ 1) ↔ (m ＝ 1) × (n ＝ 1)
_ =
  λ m n →
    ( λ H → is-one-left-is-one-mul-ℕ m n H , is-one-right-is-one-mul-ℕ m n H) ,
    ( λ (H , K) → is-one-mul-ℕ m n H K)

-- (c)
open import elementary-number-theory.addition-natural-numbers using
  ( neq-add-ℕ -- m ≠ m + (n + 1)
  )
open import elementary-number-theory.multiplication-natural-numbers using
  ( neq-mul-ℕ -- m + 1 ≠ (m + 1) * (n + 2)
  )
```

**Exercise 6.2.** Observational equality of booleans.

```agda
-- (a)
open import foundation.booleans using
  ( Eq-bool)

-- (b)
open import foundation.booleans using
  ( Eq-eq-bool
  ; eq-Eq-bool)

_ : (x y : bool) → (x ＝ y) ↔ Eq-bool x y
_ = λ x y → (Eq-eq-bool , eq-Eq-bool)

-- (c)
open import foundation.logical-operations-booleans using
  ( neq-neg-bool -- b ≠ neg-bool b
  )
_ : ¬ (false ＝ true)
_ = neq-neg-bool false
```

**Exercise 6.3.** Standard linear order on ℕ.

```agda
open import elementary-number-theory.inequality-natural-numbers using
  ( _≤-ℕ_)

-- (a)
open import elementary-number-theory.inequality-natural-numbers using
  ( refl-leq-ℕ
  ; antisymmetric-leq-ℕ
  ; transitive-leq-ℕ)

-- (b)
open import elementary-number-theory.inequality-natural-numbers using
  ( linear-leq-ℕ -- (m ≤ n) + (n ≤ m)
  )

-- (c)
open import elementary-number-theory.inequality-natural-numbers using
  ( preserves-leq-left-add-ℕ
  ; reflects-leq-left-add-ℕ)

_ : (m n k : ℕ) → (m ≤-ℕ n) ↔ (m +ℕ k ≤-ℕ n +ℕ k)
_ =
  λ m n k → (preserves-leq-left-add-ℕ k m n , reflects-leq-left-add-ℕ k m n)

-- (d)
open import elementary-number-theory.inequality-natural-numbers using
  ( preserves-leq-left-mul-ℕ
  ; reflects-leq-mul-ℕ)

_ : (m n k : ℕ) → (m ≤-ℕ n) ↔ (m *ℕ (succ-ℕ k) ≤-ℕ n *ℕ (succ-ℕ k))
_ =
  λ m n k →
    (preserves-leq-left-mul-ℕ (succ-ℕ k) m n , reflects-leq-mul-ℕ k m n)

-- (e)
open import elementary-number-theory.minimum-natural-numbers using
  ( is-greatest-lower-bound-min-ℕ -- (k ≤ min m n) ↔ (k ≤ m) × (k ≤ n)
  )
open import elementary-number-theory.maximum-natural-numbers using
  ( is-least-upper-bound-max-ℕ -- (max m n ≤ k) ↔ (m ≤ k) × (n ≤ k)
  )
```

**Exercise 6.4.** Standard strict order on ℕ.

```agda
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( _<-ℕ_)

-- (a)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( irreflexive-le-ℕ
  ; antisymmetric-le-ℕ
  ; transitive-le-ℕ)

-- (b)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( succ-le-ℕ -- n < n + 1
  ; preserves-le-succ-ℕ -- m < n → m < n + 1
  )

-- (c)
open import elementary-number-theory.strict-inequality-natural-numbers using
  ( leq-succ-le-ℕ
  ; le-leq-succ-ℕ
  ; contradiction-le-ℕ
  ; le-not-leq-ℕ)

_ : (m n : ℕ) → (m <-ℕ n) ↔ (succ-ℕ m ≤-ℕ n)
_ = λ m n → leq-succ-le-ℕ m n , le-leq-succ-ℕ m n

_ : (m n : ℕ) → (m <-ℕ n) ↔ ¬ (n ≤-ℕ m)
_ = λ m n → contradiction-le-ℕ m n , le-not-leq-ℕ m n
```

**Exercise 6.5.** Distance function on ℕ.

```agda
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ)

-- (a)
open import elementary-number-theory.distance-natural-numbers using
  ( dist-eq-ℕ
  ; eq-dist-ℕ
  ; commutative-dist-ℕ -- dist m n = dist n m
  ; triangle-inequality-dist-ℕ -- dist m n ≤ dist m k + dist k n
  )

_ : (m n : ℕ) → (m ＝ n) ↔ (dist-ℕ m n ＝ 0)
_ = λ m n → (dist-eq-ℕ m n , eq-dist-ℕ m n)

-- TODO: b

-- (c)
open import elementary-number-theory.distance-natural-numbers using
  ( translation-invariant-dist-ℕ -- dist (a + m) (a + n) = dist m n
  ; left-distributive-mul-dist-ℕ' -- dist (k * m) (k * n) = k * (dist m n)
  )

-- (d)
open import elementary-number-theory.distance-natural-numbers using
  ( is-additive-right-inverse-dist-ℕ -- x + dist x y = y for x ≤ y
  )
```

**Exercise 6.6.** The absolute value function.

```agda
open import elementary-number-theory.absolute-value-integers using
  ( abs-ℤ
  ; eq-abs-ℤ
  ; abs-eq-ℤ
  ; subadditive-abs-ℤ -- |x + y| ≤ |x| + |y|
  ; multiplicative-abs-ℤ -- |x * y| = |x| * |y|
  )

_ : (x : ℤ) → (x ＝ zero-ℤ) ↔ (abs-ℤ x ＝ 0)
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
  ( div-one-ℕ -- 1 | x
  )
```

**Proposition 7.1.5.** A 3-for-2 property of division.
<a id="proposition-7.1.5"></a>

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-add-ℕ -- d | x → d | y → d | (x + y)
  )
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
  ( cong-zero-ℕ -- k ≡ 0 mod k
  )
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

The point `⋆` is called `neg-one-Fin` because it represents the element `k - 1`
under the inclusion into ℕ.

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
  ( strict-upper-bound-nat-Fin -- ι x < k
  )
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
  ( congruence-add-ℕ -- x ≡ x' → y ≡ y' → (x + y ≡ x' + y')
  ; cong-right-summand-ℕ -- x ≡ x' → (x + y ≡ x' + y') → y ≡ y'
  ; cong-left-summand-ℕ -- y ≡ y' → (x + y ≡ x' + y') → x ≡ x'
  )
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

```agda
open import elementary-number-theory.divisibility-natural-numbers using
  ( div-right-summand-ℕ -- d | x → d | x + y → d | y
  ; div-left-summand-ℕ -- d | y → d | x + y → d | x
  )
```

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

-- (a)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin-eq
  ; eq-Eq-Fin)

_ : (k : ℕ) → {x y : Fin k} → (x ＝ y) ↔ Eq-Fin k x y
_ = λ k → (Eq-Fin-eq k , eq-Eq-Fin k)

-- (b)
open import univalent-combinatorics.standard-finite-types using
  ( is-injective-inl-Fin)

-- (c)
open import univalent-combinatorics.standard-finite-types using
  ( neq-zero-succ-Fin)

-- (d)
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

-- (a)
open import univalent-combinatorics.classical-finite-types using
  ( Eq-classical-Fin
  ; Eq-eq-classical-Fin
  ; eq-Eq-classical-Fin)

_ : (k : ℕ) → (x y : classical-Fin k) → (x ＝ y) ↔ Eq-classical-Fin k x y
_ = λ k x y → (Eq-eq-classical-Fin k x y , eq-Eq-classical-Fin k x y)

-- (b)
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

-- (a)
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( cong-mul-Fin -- ι(x * y) ≡ ι x * ι y mod (k + 1)
  )

-- (b)
open import elementary-number-theory.congruence-natural-numbers using
  ( congruence-mul-ℕ -- x ≡ x' → y ≡ y' → (x * y) ≡ (x' * y')
  )

-- (c)
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
-- (a)
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

-- (a)
open import elementary-number-theory.finitary-natural-numbers using
  ( is-empty-based-zero-ℕ)

-- (b)
open import elementary-number-theory.finitary-natural-numbers using
  ( is-injective-convert-based-ℕ)

-- (c)
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

**Definition 8.2.1.** The Collatz function.

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

**Corollary 8.2.5.**

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

_ : (a b : ℕ) → (gcd-ℕ a b ＝ 0) ↔ (add-ℕ a b ＝ 0)
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
-- (a)
open import elementary-number-theory.goldbach-conjecture using
  ( Goldbach-conjecture)

-- (b)
open import elementary-number-theory.twin-prime-conjecture using
  ( twin-prime-conjecture)

-- (c)
open import elementary-number-theory.collatz-conjecture using
  ( Collatz-conjecture)
```

**Exercise 8.2.** `is-decidable` is idempotent.

```agda
open import foundation.decidable-types using
  ( map-idempotent-is-decidable -- is-decidable (is-decidable P) → is-decidable P
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

Note that observational equality of coproducts is defined as a bespoke inductive
type, because the book definition requires raising universe levels: if `A : 𝒰`
and `B : 𝒱` aren't assumed to be in the same universe, then we need to raise the
identity type of `A`, the identity type of `B`, and the empty type to `𝒰 ⊔ 𝒱`.

```agda
module _
  {A B : UU}
  where

  Eq-copr : (x y : A + B) → UU
  Eq-copr (inl x) (inl x') = x ＝ x'
  Eq-copr (inl x) (inr y') = empty
  Eq-copr (inr y) (inl x') = empty
  Eq-copr (inr y) (inr y') = y ＝ y'

  -- (a)
  open import foundation.equality-coproduct-types using
    ( Eq-eq-coproduct
    ; eq-Eq-coproduct)

  refl-Eq-copr : (x : A + B) → Eq-copr x x
  refl-Eq-copr (inl x) = refl
  refl-Eq-copr (inr y) = refl

  Eq-eq-copr : (x y : A + B) → x ＝ y → Eq-copr x y
  Eq-eq-copr x ._ refl = refl-Eq-copr x

  eq-Eq-copr : (x y : A + B) → Eq-copr x y → x ＝ y
  eq-Eq-copr (inl x) (inl x') p = ap inl p
  eq-Eq-copr (inr y) (inr y') p = ap inr p

  _ : (x y : A + B) → (x ＝ y) ↔ Eq-copr x y
  _ = λ x y → (Eq-eq-copr x y , eq-Eq-copr x y)

  -- TODO the rest

  -- (b)
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

**Exercise 8.13.** There are infinitely many primes `p ≡ 3 mod 4`.

TODO.

**Exercise 8.14.** Prime fields.

TODO.

**Exercise 8.15.** The cofibonacci sequenece.

```agda
open import elementary-number-theory.cofibonacci using
  ( cofibonacci
  ; forward-is-left-adjoint-cofibonacci)

-- TODO: backward direction of the adjointness equivalence
```

## 9 Equivalences

### 9.1 Homotopies

**Definition 9.1.2.** Homotopies.

```agda
open import foundation.homotopies using
  ( _~_)
```

**Example 9.1.3.** `neg-bool` is an involution.

```agda
open import foundation.logical-operations-booleans using
  ( is-involution-neg-bool -- neg-bool ∘ neg-bool ~ id
  )
```

**Remark 9.1.4.** Commuting triangles and squares.

```agda
open import foundation.commuting-triangles-of-maps using
  ( coherence-triangle-maps)
open import foundation.commuting-squares-of-maps using
  ( coherence-square-maps)
```

**Definition 9.1.5.** Homotopies as an equivalence relation.

```agda
open import foundation.homotopies using
  ( refl-htpy -- f ~ f
  ; inv-htpy -- (f ~ g) → (g ~ f)
  ; concat-htpy ; _∙h_ -- (f ~ g) → (g ~ h) → f ~ h
  )
```

**Proposition 9.1.6.** Groupoid laws.

```agda
open import foundation.homotopies using
  ( assoc-htpy -- (H ∙ K) ∙ L ~ H ∙ (K ∙ L)
  ; left-unit-htpy -- refl-htpy ∙ H ~ H
  ; right-unit-htpy -- H ∙ refl-htpy ~ H
  ; left-inv-htpy -- H⁻¹ ∙ H ~ refl-htpy
  ; right-inv-htpy -- H ∙ H⁻¹ ~ refl-htpy
  )
```

**Definition 9.1.7.** Whiskering.

```agda
open import foundation.whiskering-homotopies-composition using
  ( _·l_ -- (f ~ g) → h ∘ f ~ h ∘ g
  ; _·r_ -- (g ~ h) → g ∘ f ~ h ∘ f
  )
```

## 9.2 Bi-invertible maps

**Definition 9.2.1.** Sections, retractions, equivalences.

```agda
open import foundation.sections using
  ( section)
open import foundation.retractions using
  ( retraction)
open import foundation.retracts-of-types using
  ( retract)
open import foundation.equivalences using
  ( is-equiv
  ; _≃_
  ; map-equiv -- the underlying map of e
  ; is-equiv-map-equiv
  ; map-inv-equiv -- e⁻¹
  )
```

**Example 9.2.3.** The identity equivalence.

```agda
open import foundation.equivalences using
  ( id-equiv -- A ≃ A
  )
```

**Example 9.2.4.** The negation equivalence on booleans.

```agda
open import foundation.logical-operations-booleans using
  ( equiv-neg-bool)
```

**Example 9.2.5.** The successor and predecessor equivalences on ℤ.

```agda
open import elementary-number-theory.integers using
  ( equiv-succ-ℤ
  ; equiv-pred-ℤ)
open import elementary-number-theory.addition-integers using
  ( equiv-right-add-ℤ -- x ↦ x + k
  )
open import elementary-number-theory.integers using
  ( equiv-neg-ℤ -- x ↦ -x
  )
```

**Remark 9.2.6.** Invertible maps.

```agda
open import foundation.invertible-maps using
  ( is-invertible -- has-inverse
  )
open import foundation.equivalences using
  ( is-equiv-is-invertible' -- has-inverse(f) → is-equiv(f)
  )
```

**Proposition 9.2.7.** Equivalences induce invertible maps.

```agda
open import foundation.equivalences using
  ( is-invertible-is-equiv -- is-equiv(f) → has-inverse(f)
  )
```

**Corollary 9.2.8.** Inverses of equivalences are equivalences.

```agda
open import foundation.equivalences using
  ( is-equiv-map-inv-equiv -- is-equiv(e⁻¹)
  )
```

**Example 9.2.9** Type arithmetic.

```agda
open import foundation.type-arithmetic-empty-type using
  ( left-unit-law-coproduct -- ∅ + B ≃ B
  ; right-unit-law-coproduct -- A + ∅ ≃ A
  ; left-zero-law-product -- ∅ × B ≃ ∅
  ; right-zero-law-product -- A × ∅ ≃ ∅
  )
open import foundation.type-arithmetic-unit-type using
  ( left-unit-law-product -- 𝟏 × B ≃ B
  ; right-unit-law-product -- A × 𝟏 ≃ B
  )
open import foundation.type-arithmetic-coproduct-types using
  ( commutative-coproduct -- A + B ≃ B + A
  ; associative-coproduct -- (A + B) + C ≃ A + (B + C)
  ; left-distributive-product-coproduct -- A × (B + C) ≃ (A × B) + (A × C)
  ; right-distributive-product-coproduct -- (A + B) × C ≃ (A × C) + (B × C)
  )
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-product -- A × B ≃ B × A
  ; associative-product -- (A × B) × C ≃ A × (B × C)
  )
```

**Example 9.2.10.** Type arithmetic with Σ-types.

```agda
open import foundation.type-arithmetic-empty-type using
  ( left-absorption-Σ -- Σ ∅ B ≃ ∅
  ; right-absorption-Σ -- Σ A ∅ ≃ ∅
  )
open import foundation.type-arithmetic-unit-type using
  ( left-unit-law-Σ -- Σ 𝟏 B ≃ B(⋆)
  ; right-unit-law-product -- Σ A 𝟏 ≃ A
  )
open import foundation.type-arithmetic-dependent-pair-types using
  ( associative-Σ -- Σ (Σ A B) C ≃ Σ A (λ a → Σ (B a) (λ b → C (a , b)))
  ; associative-Σ' -- Σ ((a , b) : Σ A B) (C a b) ≃ Σ (a : A) Σ (b : B) (C a b)
  )
open import foundation.type-arithmetic-coproduct-types using
  ( left-distributive-Σ-coproduct -- Σ A (λ a → B a + C a) ≃ (Σ A B) + (Σ A C)
  ; right-distributive-Σ-coproduct
    --^ Σ (A + B) C ≃ (Σ A (λ a → C (inl a))) + (Σ B (λ b → C (inr b)))
  )
```

### 9.3 Characterizing the identity types of Σ-types

**Definition 9.3.1.** Observational equality of dependent pairs.

```agda
open import foundation.equality-dependent-pair-types using
  ( Eq-Σ)
```

**Lemma 9.3.2.** `Eq-Σ` is reflexive.

```agda
open import foundation.equality-dependent-pair-types using
  ( refl-Eq-Σ)
```

**Definition 9.3.3.** Equality induces observational equality.

```agda
open import foundation.equality-dependent-pair-types using
  ( pair-eq-Σ)
```

**Theorem 9.3.4.** `pair-eq` is an equivalence.

Note that the inverse map `eq-pair-Σ` is not defined by pattern matching on both
components. Instead, we only pattern match on the first identification, and then
construct `s ＝ t → (x , s) ＝ (x , t)` by applying `(x , -)`.

```agda
open import foundation.equality-dependent-pair-types using
  ( eq-pair-Σ' ; eq-pair-Σ
  ; equiv-pair-eq-Σ)
```

### Exercises

**Exercise 9.1.** Operations on identifications are equivalences.

```agda
open import foundation.identity-types using
  ( equiv-inv -- p ↦ p⁻¹
  ; equiv-concat -- q ↦ p ∙ q
  ; equiv-concat' -- r ↦ r ∙ p
  )
open import foundation.transport-along-identifications using
  ( equiv-tr -- (x ＝ y) → B x ≃ B y
  )
```

**Exercise 9.2.** Non-equivalences.

```agda
-- (a)
open import foundation.booleans using
  ( is-not-equiv-const-bool -- const(b) is not an equivalence
  )

-- (b)
open import foundation.booleans using
  ( is-not-unit-bool -- bool ≄ 𝟏
  )

-- (c)
open import univalent-combinatorics.pigeonhole-principle using
  ( no-equiv-ℕ-Fin)
```

**Exercise 9.3.** Homotopies and equivalences.

```agda
-- (a)
open import foundation.equivalences using
  ( is-equiv-htpy
  ; is-equiv-htpy')

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  (f ~ g) → is-equiv f ↔ is-equiv g
_ = λ H → is-equiv-htpy' _ H , is-equiv-htpy _ H

-- (b)
open import foundation.equivalences using
  ( htpy-map-inv-is-equiv)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ≃ B) →
  map-equiv f ~ map-equiv g → map-inv-equiv f ~ map-inv-equiv g
_ =
  λ f g H →
    htpy-map-inv-is-equiv H (is-equiv-map-equiv f) (is-equiv-map-equiv g)
```

**Exercise 9.4.** The 3-for-2 property of equivalences.

```agda
-- (a)
open import foundation.commuting-triangles-of-maps using
  ( triangle-section)
open import foundation.sections using
  ( section-right-map-triangle
  ; section-left-map-triangle)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (s : section h) →
  coherence-triangle-maps f g h →
  section f ↔ section g
_ =
  λ f g h s H →
    section-right-map-triangle f g h H , section-left-map-triangle f g h H s

-- (b)
open import foundation.commuting-triangles-of-maps using
  ( triangle-retraction)
open import foundation.retractions using
  ( retraction-top-map-triangle
  ; retraction-left-map-triangle)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (r : retraction g) →
  coherence-triangle-maps f g h →
  retraction f ↔ retraction h
_ =
  λ f g h r H →
    retraction-top-map-triangle f g h H , retraction-left-map-triangle f g h H r

-- (c)
open import foundation.equivalences using
  ( is-equiv-left-map-triangle -- is-equiv h → is-equiv g → is-equiv f
  ; is-equiv-right-map-triangle -- is-equiv f → is-equiv h → is-equiv g
  ; is-equiv-top-map-triangle -- is-equiv g → is-equiv f → is-equiv h
  ; is-equiv-is-section
  ; is-equiv-is-retraction
  ; _∘e_ -- in particular, equivalences compose
  )
```

**Exercise 9.5.** Swapping equivalences of Σ-types.

```agda
-- (a)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-left-swap-Σ)

-- (b)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-right-swap-Σ)
```

**Exercise 9.6.** Functoriality of coproducts.

```agda
-- (a)
open import foundation.functoriality-coproduct-types using
  ( id-map-coproduct -- id + id ~ id
  )

-- (b)
open import foundation.functoriality-coproduct-types using
  ( preserves-comp-map-coproduct -- (f' ∘ f) + (g' ∘ g) ~ (f' + g') ∘ (f + g)
  )

-- (c)
open import foundation.functoriality-coproduct-types using
  ( htpy-map-coproduct -- H + K : (f + g) ~ (f' + g')
  )

-- (d)
open import foundation.functoriality-coproduct-types using
  ( is-equiv-map-coproduct ; equiv-coproduct)
```

**Exercise 9.7.** Functoriality of products.

```agda
-- (a)
open import foundation.functoriality-cartesian-product-types using
  ( map-product -- f × g : A × B → A' × B'
  )

-- (b)
open import foundation.functoriality-cartesian-product-types using
  ( map-product-id -- id × id ~ id
  )

-- (c)
open import foundation.functoriality-cartesian-product-types using
  ( preserves-comp-map-product -- (f' ∘ f) × (g' ∘ g) ~ (f' × g') ∘ (f × g)
  )

-- (d)
open import foundation.functoriality-cartesian-product-types using
  ( htpy-map-product -- H × K : f × g ~ f' × g'
  )
```

TODO: report this

The claim of part (e) is actually false. We cannot construct the inverse map, as
evidenced by the following counterexample: consider `ex-falso : ∅ → 𝟏`. By
induction on ∅ we get a proof of `∅ → is-equiv ex-falso`, and assuming the
exercise holds, we get an equivalence `∅ × ∅ ≃ 𝟏 × 𝟏`, from which we can easily
derive a contradiction.

```agda
_ :
  ( {l1 l2 l3 l4 : Level} (A : UU l1) (B : UU l2) (A' : UU l3) (B' : UU l4)
    (f : A → A') (g : B → B') →
    (B → is-equiv f) × (A → is-equiv g) →
    is-equiv (map-product f g)) →
  empty
_ =
  λ H →
    pr1
      ( map-inv-equiv
        ( map-product ex-falso ex-falso ,
          H empty empty unit unit ex-falso ex-falso (ex-falso , ex-falso))
        ( star , star))
```

The correct statement has `B'` and `A'` instead of `B` and `A` in proposition
(ii).

```agda
-- (e)
open import foundation.functoriality-cartesian-product-types using
  ( is-equiv-map-product'
  ; is-equiv-left-factor-is-equiv-map-product'
  ; is-equiv-right-factor-is-equiv-map-product')
_ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
  (f : A → A') (g : B → B') →
  is-equiv (map-product f g) ↔ (B' → is-equiv f) × (A' → is-equiv g)
_ =
  λ f g →
    ( λ H →
      ( λ b' → is-equiv-left-factor-is-equiv-map-product' f g b' H) ,
      ( λ a' → is-equiv-right-factor-is-equiv-map-product' f g a' H)) ,
    ( λ (F , G) → is-equiv-map-product' f g F G)
```

The proof of the forward direction in the library uses the characterization of
equivalences as contractible maps, which is Theorems [10.3.5](#theorem-10.3.5)
and [10.4.6](#theorem-10.5.6). This characterization isn't available at this
point in the book, so a "nuts and bolts" proof is included below.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4}
  (f : A → A') (g : B → B') (H : is-equiv (map-product f g))
  where private
  open import foundation.equivalences

  map-inv-f : B' → (A' → A)
  map-inv-f b' a' = pr1 (map-inv-is-equiv H (a' , b'))

  map-inv-g : A' → (B' → B)
  map-inv-g a' b' = pr2 (map-inv-is-equiv H (a' , b'))

  is-section-map-inv-f : (b' : B') → f ∘ map-inv-f b' ~ id
  is-section-map-inv-f b' a' = ap pr1 (is-section-map-inv-is-equiv H (a' , b'))

  is-section-map-inv-g : (a' : A') → g ∘ map-inv-g a' ~ id
  is-section-map-inv-g a' b' = ap pr2 (is-section-map-inv-is-equiv H (a' , b'))

  is-retraction-map-inv-f : (b' : B') → map-inv-f b' ∘ f ~ id
  is-retraction-map-inv-f b' a =
    ap pr1
      ( ( ap
          ( λ x → map-inv-is-equiv H (f a , x))
          ( inv (is-section-map-inv-g (f a) b'))) ∙
        ( is-retraction-map-inv-is-equiv H
          ( a , map-inv-g (f a) b')))

  is-retraction-map-inv-g : (a' : A') → map-inv-g a' ∘ g ~ id
  is-retraction-map-inv-g a' b =
    ap pr2
      ( ( ap
          ( λ x → map-inv-is-equiv H (x , g b))
          ( inv (is-section-map-inv-f (g b) a'))) ∙
        ( is-retraction-map-inv-is-equiv H
          ( map-inv-f (g b) a' , b)))

  is-equiv-f : B' → is-equiv f
  is-equiv-f b' =
    is-equiv-is-invertible
      ( map-inv-f b')
      ( is-section-map-inv-f b')
      ( is-retraction-map-inv-f b')

  is-equiv-g : A' → is-equiv g
  is-equiv-g a' =
    is-equiv-is-invertible
      ( map-inv-g a')
      ( is-section-map-inv-g a')
      ( is-retraction-map-inv-g a')
```

**Exercise 9.8.** Finite type arithmetic.

```agda
open import univalent-combinatorics.coproduct-types using
  ( inv-compute-coproduct-Fin -- Fin (k + l) ≃ Fin k + Fin l
  )
open import univalent-combinatorics.cartesian-product-types using
  ( Fin-mul-ℕ -- Fin (k * l) ≃ Fin k × Fin l
  )
```

**Exercise 9.9.** Finitely cyclic maps.

```agda
open import elementary-number-theory.finitely-cyclic-maps using
  ( is-finitely-cyclic-map)

-- (a)
open import elementary-number-theory.finitely-cyclic-maps using
  ( is-equiv-is-finitely-cyclic-map)

-- (b)
open import elementary-number-theory.finitely-cyclic-maps using
  ( is-finitely-cyclic-succ-Fin)
```

## 10 Contractible types and contractible maps

### 10.1 Contractible types

**Definition 10.1.1.** Contractible types.

```agda
open import foundation.contractible-types using
  ( is-contr
  ; center
  ; contraction)
```

**Example 10.1.3.** 𝟏 is contractible.

```agda
open import foundation.unit-type using
  ( is-contr-unit)
```

**Theorem 10.1.4.** Contractibility of singletons.

```agda
open import foundation.torsorial-type-families using
  ( is-torsorial-Id)
```

### 10.2 Singleton induction

**Definition 10.2.1.** Singleton induction.

```agda
open import foundation.singleton-induction using
  ( is-singleton
  ; ind-is-singleton -- ind-sing
  ; compute-ind-is-singleton -- comp-sing
  )
```

**Example 10.2.2.** 𝟏 satisfies singleton induction.

```agda
open import foundation.unit-type using
  ( is-singleton-unit)
```

**Theorem 10.2.3.** A type is contractible if and only if it is a singleton.

We do not include a proof of the logical equivalence, because singleton
elimination is a statement of the form "for all type families", which makes it a
[large type](https://agda.readthedocs.io/en/v2.7.0.1/language/sort-system.html#sorts-seti),
so it cannot appear on either side of `_↔_`, which only quantifies over small
types.

```agda
open import foundation.singleton-induction using
  ( is-singleton-is-contr -- is-contr A → is-singleton A
  ; is-contr-is-singleton -- is-singleton A → is-contr A
  )
```

### 10.3 Contractible maps

**Definition 10.3.1.** Fibers of maps.

```agda
open import foundation.fibers-of-maps using
  ( fiber -- fib
  )
```

**Definition 10.3.2.** Observational equality of fibers.

```agda
open import foundation.fibers-of-maps using
  ( Eq-fiber -- Eq-fib
  ; refl-Eq-fiber
  )
```

**Proposition 10.3.3.** Characterization of identity types of fibers.

```agda
open import foundation.fibers-of-maps using
  ( is-equiv-Eq-eq-fiber)
```

**Definition 10.3.4.** Contractible maps.

```agda
open import foundation.contractible-maps using
  ( is-contr-map -- is-contr
  )
```

**Theorem 10.3.5.** Any contractible map is an equivalence.
<a id="theorem-10.3.5"></a>

```agda
open import foundation.contractible-maps using
  ( is-equiv-is-contr-map -- is-contr f → is-equiv f
  )
```

### 10.4 Equivalences are contractible maps

**Definition 10.4.1.** Coherently invertible maps.

```agda
open import foundation.coherently-invertible-maps using
  ( is-coherently-invertible -- is-coh-invertible
  )
```

**Proposition 10.4.2.** Coherently invertible maps are contractible.

```agda
open import foundation.contractible-maps using
  ( is-contr-map-is-coherently-invertible)
```

**Definition 10.4.3.** Naturality squares of homotopies.

Note that `nat-htpy` in the library goes in the other direction that the one in
the book, so the book's `nat-htpy` is called `inv-nat-htpy` here.

```agda
open import foundation.homotopies using
  ( inv-nat-htpy)
```

**Definition 10.4.4.** Naturality for homotopies `H : f ~ id`.

```agda
open import foundation.whiskering-homotopies-composition using
  ( coh-htpy-id)
```

**Lemma 10.4.5.** Improving invertible maps to coherently invertible maps.

```agda
open import foundation.coherently-invertible-maps using
  ( is-coherently-invertible-is-invertible)
```

**Theorem 10.4.6.** Any equivalence is a contractible map.
<a id="theorem-10.4.6"></a>

```agda
open import foundation.contractible-maps using
  ( is-contr-map-is-equiv)
```

**Corollary 10.4.7.** `Σ A (λ x → x = a)` is contractible.

The statement is proven by induction in the library. The book's proof goes as
follows:

```agda
_ : {l : Level} {A : UU l} (a : A) → is-contr (Σ A (λ x → x ＝ a))
_ = is-contr-map-is-equiv (is-equiv-map-equiv id-equiv)
```

### Exercises

**Exercise 10.1.** Contractible types have contractible identity types.

As explained in Section 12, types with contractible identity types are called
propositions, hence the name of this definition.

```agda
open import foundation.contractible-types using
  ( is-prop-is-contr)
```

**Exercise 10.2.** Retracts of contractible types are contractible.

```agda
open import foundation.contractible-types using
  ( is-contr-retract-of)
```

**Exercise 10.3.** Uniqueness of contractible types.

```agda
-- (a)
open import foundation.unit-type using
  ( terminal-map -- const* : A → 𝟏
  ; is-contr-is-equiv-terminal-map
  ; is-equiv-terminal-map-is-contr)

_ : {l : Level} {A : UU l} → is-equiv (terminal-map A) ↔ is-contr A
_ = is-contr-is-equiv-terminal-map , is-equiv-terminal-map-is-contr

-- (b)
open import foundation.contractible-types using
  ( is-equiv-is-contr -- is-contr A → is-contr B → is-equiv f
  ; is-contr-is-equiv -- is-equiv f → is-contr B → is-contr A
  ; is-contr-is-equiv' -- is-equiv f → is-contr A → is-contr B
  ; is-contr-equiv
  )
```

The proofs in the library don't use the 3-for-2 property of equivalences as
required in the exercise, so those are included below:

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where private

  triangle : coherence-triangle-maps (terminal-map A) (terminal-map B) f
  triangle = refl-htpy

  _ : is-contr A → is-contr B → is-equiv f
  _ =
    λ H K →
      is-equiv-top-map-triangle _ _ _
        ( triangle)
        ( is-equiv-terminal-map-is-contr K)
        ( is-equiv-terminal-map-is-contr H)

  _ : is-equiv f → is-contr B → is-contr A
  _ =
    λ L K →
      is-contr-is-equiv-terminal-map
        ( is-equiv-left-map-triangle _ _ _
          ( triangle)
          ( L)
          ( is-equiv-terminal-map-is-contr K))

  _ : is-equiv f → is-contr A → is-contr B
  _ =
    λ L H →
      is-contr-is-equiv-terminal-map
        ( is-equiv-right-map-triangle _ _ _
          ( triangle)
          ( is-equiv-terminal-map-is-contr H)
          ( L))
```

**Exercise 10.4.** `Fin k` is not contractible for `k ≠ 1`.

```agda
open import univalent-combinatorics.standard-finite-types using
  ( is-not-contractible-Fin)
```

**Exercise 10.5.** Contractibility of cartesian product types.

```agda
open import foundation.contractible-types using
  ( is-contr-product
  ; is-contr-left-factor-product
  ; is-contr-right-factor-product)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (is-contr A × is-contr B) ↔ is-contr (A × B)
_ =
  ( λ (H , K) → is-contr-product H K) ,
  ( λ H →
    ( is-contr-left-factor-product _ _ H , is-contr-right-factor-product _ _ H))
```

**Exercise 10.6.** The left unit law of Σ-types.

```agda
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-equiv-map-inv-left-unit-law-Σ-is-contr)
```

**Exercise 10.7.**

```agda
-- (a)
open import foundation.fibers-of-maps using
  ( is-equiv-map-fiber-pr1)

-- (b)
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-contr-is-equiv-pr1
  ; is-equiv-pr1-is-contr)

_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (pr1 {B = B}) ↔ ((x : A) → is-contr (B x))
_ = is-contr-is-equiv-pr1 , is-equiv-pr1-is-contr

-- (c)
open import foundation.sections using
  ( map-section-family
  ; is-contr-fam-is-equiv-map-section-family
  ; is-equiv-map-section-family)

_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-equiv (map-section-family b) ↔ ((x : A) → is-contr (B x))
_ =
  λ b →
    is-contr-fam-is-equiv-map-section-family b , is-equiv-map-section-family b
```

**Exercise 10.8.** Fibrant replacement.

```agda
open import foundation.fibers-of-maps using
  ( inv-equiv-total-fiber -- A ≃ Σ B (fib f)
  )

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  coherence-triangle-maps f pr1 (map-equiv (inv-equiv-total-fiber f))
_ = λ f → refl-htpy
```

## 11 The fundamental theorem of identity types

### 11.1 Families of equivalences

**Definition 11.1.1.** Induced maps of total spaces.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( tot)
```

**Lemma 11.1.2.** Fibers of `tot f`.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( compute-fiber-tot)
```

**Theorem 11.1.3.** `f` is a family of equivalences if and only if `tot f` is an
equivalence.

```agda
open import foundation.families-of-equivalences using
  ( is-fiberwise-equiv)
open import foundation.functoriality-dependent-pair-types using
  ( is-equiv-tot-is-fiberwise-equiv
  ; is-fiberwise-equiv-is-equiv-tot)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x} →
  ((x : A) → is-equiv (f x)) ↔ is-equiv (tot f)
_ = is-equiv-tot-is-fiberwise-equiv , is-fiberwise-equiv-is-equiv-tot
```

**Lemma 11.1.4.** If `f` is an equivalence, then `σf` is an equivalence.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( map-Σ-map-base -- σ
  ; is-equiv-map-Σ-map-base
  )
```

**Definition 11.1.5.** Bifunctoriality of dependent pair types.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( map-Σ -- tot f g
  )
```

**Theorem 11.1.6.** A family of maps `g` over an equivalence is a family of
equivalences if and only if `tot f g` is an equivalence.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( is-equiv-map-Σ
  ; is-fiberwise-equiv-is-equiv-map-Σ)

_ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  {f : A → B} {g : (x : A) → C x → D (f x)} → is-equiv f →
  ((x : A) → is-equiv (g x)) ↔ is-equiv (map-Σ D f g)
_ = λ D H → is-equiv-map-Σ D H , is-fiberwise-equiv-is-equiv-map-Σ D _ _ H
```

### 11.2 The fundamental theorem

**Definition 11.2.1.** Unary identity systems.

```agda
open import foundation.identity-systems using
  ( is-identity-system)
```

**Theorem 11.2.2.** The fundamental theorem of identity types.

```agda
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id -- (ii) → (i)
  ; fundamental-theorem-id' -- (i) → (ii)
  )
open import foundation.identity-systems using
  ( is-identity-system-is-torsorial -- (ii) → (iii)
  ; fundamental-theorem-id-is-identity-system -- (iii) → (i)
  )
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-J -- the particular case
  ; fundamental-theorem-id-J'
  )
```

### 11.3 Equality on the natural numbers

**Theorem 11.3.1.** Characterization of equality of natural numbers.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( is-equiv-Eq-eq-ℕ)
```

### 11.4 Embeddings

**Definition 11.4.1.** Embeddings.

```agda
open import foundation.embeddings using
  ( is-emb
  ; _↪_)
```

**Theorem 11.4.2.** Any equivalence is an embedding.

```agda
open import foundation.equivalences using
  ( is-emb-is-equiv)
```

### 11.5 Disjointness of coproducts

**Definition 11.5.2.** Observational equality of coproducts.

TODO: report that `Eq-copr` has already been defined in Exercise 8.7?

```agda
_ = Eq-copr
```

**Lemma 11.5.3.** Reflexivity of `Eq-copr`.

```agda
_ = refl-Eq-copr
```

**Proposition 11.5.4.** Torsoriality of observational equality of coproducts.

```agda
is-torsorial-Eq-copr :
  {A B : UU} (s : A + B) → is-contr (Σ (A + B) (λ t → Eq-copr s t))
is-torsorial-Eq-copr {A} {B} (inl x) =
  is-contr-equiv
    ( Σ A (λ x' → x ＝ x'))
    ( right-unit-law-coproduct (Σ A (λ x' → x ＝ x')) ∘e
      equiv-coproduct id-equiv (right-zero-law-product B) ∘e
      right-distributive-Σ-coproduct (Eq-copr (inl x)))
    ( is-torsorial-Id x)
is-torsorial-Eq-copr {A} {B} (inr y) =
  is-contr-equiv
    ( Σ B (λ y' → y ＝ y'))
    ( left-unit-law-coproduct (Σ B (λ y' → y ＝ y')) ∘e
      equiv-coproduct (right-zero-law-product A) id-equiv ∘e
      right-distributive-Σ-coproduct (Eq-copr (inr y)))
    ( is-torsorial-Id y)
```

**Theorem 11.5.1.** Characterization of equality of coproducts.

```agda
is-equiv-Eq-eq-copr : {A B : UU} (x y : A + B) → is-equiv (Eq-eq-copr x y)
is-equiv-Eq-eq-copr x =
  fundamental-theorem-id (is-torsorial-Eq-copr x) (Eq-eq-copr x)

equiv-Eq-eq-copr : {A B : UU} (x y : A + B) → (x ＝ y) ≃ (Eq-copr x y)
pr1 (equiv-Eq-eq-copr x y) = Eq-eq-copr x y
pr2 (equiv-Eq-eq-copr x y) = is-equiv-Eq-eq-copr x y

module _
  {A B : UU}
  where

  private variable
    x x' : A
    y y' : B

  _ : (inl {B = B} x ＝ inl x') ≃ (x ＝ x')
  _ = equiv-Eq-eq-copr (inl _) (inl _)

  _ : (inl x ＝ inr y') ≃ empty
  _ = equiv-Eq-eq-copr (inl _) (inr _)

  _ : (inr y ＝ inl x') ≃ empty
  _ = equiv-Eq-eq-copr (inr _) (inl _)

  _ : (inr {A = A} y ＝ inr y') ≃ (y ＝ y')
  _ = equiv-Eq-eq-copr (inr _) (inr _)
```

### 11.6 The structure identity principle

**Definition 11.6.1.** Dependent identity systems.

TODO, apparently?

**Theorem 11.6.2.** The structure identity principle.

TODO as stated? We use torsoriality instead of dependent identity systems.

```agda
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
```

**Example 11.6.3.** Characterization of equality of fibers.

TODO: report "alternative characterization of the fiber" should probably say
"equality"

TODO: do we have access to `equiv-right-transpose-eq-concat`?

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  open import foundation.identity-types

  alt-Eq-fiber : (x y : fiber f b) → UU (l1 ⊔ l2)
  alt-Eq-fiber (x , p) (y , q) = fiber (ap f) (p ∙ inv q)

  refl-alt-Eq-fiber : (x : fiber f b) → alt-Eq-fiber x x
  refl-alt-Eq-fiber (x , p) = refl , (inv (right-inv p))

  _ : (x y : fiber f b) → (x ＝ y) ≃ alt-Eq-fiber x y
  _ =
    λ (x , p) →
      extensionality-Σ
        ( λ q α → ap f α ＝ p ∙ inv q)
        ( refl)
        ( inv (right-inv p))
        ( λ y → id-equiv)
        ( λ q → equiv-right-transpose-eq-concat refl q p ∘e equiv-inv p q)
```

### Exercises

**Exercise 11.1.**

```agda
-- (a)
open import foundation.empty-types using
  ( is-emb-ex-falso)

-- (b)
open import foundation.equality-coproduct-types using
  ( is-emb-inl
  ; is-emb-inr)

-- (c)
open import foundation.type-arithmetic-empty-type using
  ( is-equiv-inl-is-empty
  ; is-equiv-inr-is-empty)
```

**Exercise 11.2.** Transposing identifications along equivalences.

```agda
open import foundation.transposition-identifications-along-equivalences using
  ( eq-transpose-equiv -- (e(x) = y) ≃ (x = e⁻¹(y))
  ; triangle-eq-transpose-equiv
  )
```

**Exercise 11.3.** Being an embedding is preserved by homotopies.

```agda
open import foundation.embeddings using
  ( is-emb-htpy
  ; is-emb-htpy')

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g) →
  is-emb f ↔ is-emb g
_ = λ H → is-emb-htpy' H , is-emb-htpy H
```

**Exercise 11.4.** Triangles of embeddings.

```agda
-- (a)
open import foundation.embeddings using
  ( is-emb-top-map-triangle
  ; is-emb-left-map-triangle)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {h : A → B} (H : coherence-triangle-maps f g h) →
  is-emb g → (is-emb f ↔ is-emb h)
_ =
  λ H is-emb-g →
    is-emb-top-map-triangle _ _ _ H is-emb-g ,
    is-emb-left-map-triangle _ _ _ H is-emb-g

-- (b)
open import foundation.embeddings using
  ( is-emb-triangle-is-equiv
  ; is-emb-triangle-is-equiv')

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {h : A → B} (H : coherence-triangle-maps f g h) →
  is-equiv h → (is-emb f ↔ is-emb g)
_ =
  λ H is-equiv-h →
    is-emb-triangle-is-equiv' _ _ _ H is-equiv-h ,
    is-emb-triangle-is-equiv _ _ _ H is-equiv-h
```

**Exercise 11.5.** Composition of embeddings being equivalences.

TODO I think.

**Exercise 11.6.** `map-coproduct f g` being an embedding.

```agda
open import foundation.equality-coproduct-types using
  ( is-emb-coproduct -- f, g embeddings and f(a) ≠ g(a) → is-emb [f, g]
  )

-- TODO: reverse implication
```

**Exercise 11.7.** Equivalences and embeddings with `map-coproduct`.

```agda
-- TODO: a

-- (b)
open import foundation.functoriality-coproduct-types using
  ( is-emb-map-coproduct)

-- TODO: reverse implication
```

**Exercirse 11.8.** Functoriality of `tot`.

```agda
-- (a)
open import foundation.functoriality-dependent-pair-types using
  ( tot-htpy -- f ~ g → tot f ~ tot g
  )

-- (b)
open import foundation.functoriality-dependent-pair-types using
  ( preserves-comp-tot -- tot (g ∘ f) ~ tot g ∘ tot f
  )

-- (c)
open import foundation.functoriality-dependent-pair-types using
  ( tot-id -- tot id ~ id
  )

-- (d)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-retract)

-- (e)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-section)
```

**Exercise 11.9.** Relaxing the condition of `ap(f)` being an equivalence.

```agda
open import foundation.embeddings using
  ( is-emb-section-ap)
```

**Exercise 11.10.** Path-split maps.

TODO: this and other exercises ask the reader to "show that the following are
equivalent"; this can mean to show inverse implications, but it's also possible
to interpret it as showing a literal equivalence. That's also possible, but
would require some understanding of hProps and proofs of being one, which only
comes up in the next section. What's the intention here?

```agda
open import foundation.path-split-maps using
  ( is-path-split
  ; is-path-split-is-equiv
  ; is-equiv-is-path-split)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f ↔ is-path-split f
_ = λ f → is-path-split-is-equiv f , is-equiv-is-path-split f

-- TODO: see above if this should be included
open import foundation.path-split-maps using
  ( equiv-is-path-split-is-equiv)
```

**Exercise 11.11.** Straightening fiberwise maps.

```agda
-- (a)
open import foundation.functoriality-dependent-pair-types using
  ( fiber-triangle
  ; square-tot-fiber-triangle)

-- (b)
open import foundation.functoriality-dependent-pair-types using
  ( is-fiberwise-equiv-is-equiv-triangle
  ; is-equiv-triangle-is-fiberwise-equiv)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {h : A → B} (H : coherence-triangle-maps f g h) →
  is-equiv h ↔ is-fiberwise-equiv (fiber-triangle f g h H)
_ =
  λ H →
    is-fiberwise-equiv-is-equiv-triangle _ _ _ H ,
    is-equiv-triangle-is-fiberwise-equiv _ _ _ H
```

## 12 Propositions, sets, and the higher truncation levels

### 12.1 Propositions

**Definition 12.1.1.** Propositions.

```agda
open import foundation.propositions using
  ( is-prop
  ; Prop
  ; type-Prop)
```

**Example 12.1.2.** The unit type and the empty types are propositions.

```agda
open import foundation.unit-type using
  ( is-prop-unit)

open import foundation.empty-types using
  ( is-prop-empty)
```

**Proposition 12.1.3.** Characterizations of propositions.

Note that the library doesn't show the (iii) → (iv) step (TODO: importing the
unit type to foundation-core.propositions creates a cycle, and it feels out of
place in foundation.propositions; do we want to shuffle things around to have it
formalized?). Instead we show (i) → (ii) → (iii) → (i) and (i) ↔ (iv)

```agda
open import foundation.propositions using
  ( eq-is-prop' -- (i) → (ii)
  ; is-proof-irrelevant-all-elements-equal -- (ii) → (iii)
  ; is-prop-is-emb-terminal-map -- (iv) → (i)
  )

-- (iii) → (iv)
open import foundation.embeddings
_ :
  {l1 : Level} {A : UU l1} →
  (A → is-contr A) → is-emb (terminal-map A)
_ =
  λ PI →
    is-emb-is-emb
      ( λ a → is-emb-is-equiv (is-equiv-terminal-map-is-contr (PI a)))
```

**Proposition 12.1.4.** Two propositions are logically equivalent if and only if
they are equivalent.

```agda
open import foundation.logical-equivalences using
  ( iff-equiv
  ; equiv-iff-is-prop)

_ :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} → is-prop P → is-prop Q →
  (P ≃ Q) ↔ (P ↔ Q)
_ =
  λ H K → iff-equiv , λ (f , g) → equiv-iff-is-prop H K f g
```

### 12.2 Subtypes

**Definition 12.2.1.** Subtypes.

Note that rather than defining `subtype` to be a type family `B` equipped with a
witness of `is-subtype B`, we define subtypes to be a family of `Prop`s. The two
definitions are equivalent.

```agda
open import foundation.subtypes using
  ( is-subtype
  ; is-property
  ; subtype-is-subtype -- conversion from book subtypes to library subtypes
  )
```

**Lemma 12.2.2.** Being a proposition is closed under equivalences.

```agda
open import foundation.propositions using
  ( is-prop-equiv
  ; is-prop-equiv')

_ : {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → is-prop A ↔ is-prop B
_ = λ e → is-prop-equiv' e , is-prop-equiv e
```

**Theorem 12.2.3.** Embeddings are propositional maps.

```agda
open import foundation.propositional-maps using
  ( is-prop-map
  ; is-prop-map-is-emb
  ; is-emb-is-prop-map
  )

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} → is-prop-map f ↔ is-emb f
_ = is-emb-is-prop-map , is-prop-map-is-emb
```

**Corollary 12.2.4.** First projection being an embedding.

```agda
open import foundation.subtypes using
  ( is-subtype-is-emb-pr1
  ; is-emb-inclusion-subtype
  )

_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (is-emb (pr1 {B = B})) ↔ is-subtype B
_ =
  is-subtype-is-emb-pr1 , λ H → is-emb-inclusion-subtype (subtype-is-subtype H)
```

### 12.3 Sets

**Definition 12.3.1.** Sets.

```agda
open import foundation.sets using
  ( is-set)
```

**Example 12.3.2.** ℕ is a set.

```agda
open import elementary-number-theory.equality-natural-numbers using
  ( is-set-ℕ)
```

**Proposition 12.3.3.** Sets are exactly types satisfying axiom K.

```agda
open import foundation.sets using
  ( instance-axiom-K
  ; axiom-K-is-set
  ; is-set-axiom-K)

_ : {l1 : Level} {A : UU l1} → is-set A ↔ instance-axiom-K A
_ = axiom-K-is-set , is-set-axiom-K
```

**Proposition 12.3.4.** A type with a reflexive relation mapping into its
identity types is a set.

```agda
open import foundation.sets using
  ( is-set-prop-in-id)
```

**Theorem 12.3.5.** Hedberg's theorem: any type with decidable equality is a
set.

```agda
open import foundation.decidable-equality using
  ( is-set-has-decidable-equality)
```

### 12.4 General truncation levels

```agda
open import foundation.truncation-levels using
  ( 𝕋 -- the indexing type of truncation levels
  ; neg-two-𝕋 -- -2_𝕋, -2
  ; succ-𝕋 -- succ_𝕋, k + 1
  ; truncation-level-ℕ -- inclusion mapping 0 to -2+1+1
  )
```

**Definition 12.4.1.** `k`-truncated types and maps.

TODO: we don't have _proper_ `(k+1)` types; are they not useful?

```agda
open import foundation.truncated-types using
  ( is-trunc
  ; Truncated-Type -- 𝒰≤ᵏ
  )

open import foundation.truncated-maps using
  ( is-trunc-map)
```

**Proposition 12.4.3.** Truncation levels are cumulative.

```agda
open import foundation.truncated-types using
  ( is-trunc-succ-is-trunc -- is-trunc k A → is-trunc (k+1) A
  )
```

**Corollary 12.4.4.** `k`-types have `k`-truncated identity types.

```agda
open import foundation.truncated-types using
  ( is-trunc-Id)
```

**Proposition 12.4.5.** Being a `k`-type is preserved by equivalences.

```agda
open import foundation.truncated-types using
  ( is-trunc-equiv -- A ≃ B → is-trunc k B → is-trunc k A
  )
```

**Corollary 12.4.6.** Being a `k+1`-type is reflected by embeddings.

```agda
open import foundation.truncated-types using
  ( is-trunc-emb -- A ↪ B → is-trunc (k+1) B → is-trunc (k+1) A
  )
```

**Theorem 12.4.7.** Recursive characterization of `(k+1)`-truncated maps.

TODO: report that the last line of equivalence reasoning is on the next page.

```agda
open import foundation.truncated-maps using
  ( is-trunc-map-ap-is-trunc-map-succ
  ; is-trunc-map-succ-is-trunc-map-ap)

_ :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  (is-trunc-map (succ-𝕋 k) f) ↔ ((x y : A) → is-trunc-map k (ap f {x} {y}))
_ =
  λ k f →
    is-trunc-map-ap-is-trunc-map-succ k f ,
    is-trunc-map-succ-is-trunc-map-ap k f
```

### Exercises

**Exercise 12.1.** The type of booleans is a set.

```agda
open import foundation.booleans using
  ( is-set-bool)
```

**Exercise 12.2.** The underlying type of a poset is a set.

```agda
open import order-theory.posets using
  ( is-set-type-Poset)
```

**Exercise 12.3.** Embeddings of natural numbers.

Note that in `(a)`, the library has a direct proof of the second part, and uses
it in the proof of the first part, rather than the other way around.

TODO: "injective maps" isn't actually ever properly defined AFAICT.

```agda
-- (a)
open import foundation.injective-maps using
  ( is-emb-is-injective)

open import foundation.sets using
  ( is-set-is-injective)

-- Proof of the conclusion following the book
open import foundation.injective-maps using
  ( is-injective)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-set B → is-injective f → is-set A
_ = λ H K → is-trunc-emb (succ-𝕋 neg-two-𝕋) (_ , is-emb-is-injective H K) H

-- (b)
open import elementary-number-theory.addition-natural-numbers using
  ( is-emb-left-add-ℕ -- λ n → m + n is an embedding
  )

-- Note: the library uses (k + m = n) rather than (m + k = n)
open import elementary-number-theory.difference-natural-numbers using
  ( subtraction-leq-ℕ
  ; leq-subtraction-ℕ)

-- TODO: conclude equivalence
_ :
  (m n : ℕ) → (m ≤-ℕ n) ↔ Σ ℕ (λ k → k +ℕ m ＝ n)
_ =
  λ m n → subtraction-leq-ℕ m n , λ (k , H) → leq-subtraction-ℕ m n k H

-- (c)
open import elementary-number-theory.multiplication-natural-numbers using
  ( is-emb-left-mul-ℕ -- λ n → mn is an embedding for m ≠ 0
  )

open import elementary-number-theory.divisibility-natural-numbers using
  ( is-prop-div-ℕ)
```

**Exercise 12.4.** Coproducts of truncated types.

```agda
-- (a)
open import foundation.coproduct-types using
  ( is-not-contractible-coproduct-is-contr)

-- Note: the library calls the book's exclusive disjunction "exclusive sums",
-- and the name "exclusive disjunction" is used for the type is-contr (P + Q)
-- (b)
open import foundation.exclusive-disjunction using
  ( equiv-exclusive-sum-xor-Prop)

_ :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  is-contr (type-Prop P + type-Prop Q) ↔
  (type-Prop P × ¬ (type-Prop Q)) + type-Prop Q × ¬ (type-Prop P)
_ = λ P Q → iff-equiv (equiv-exclusive-sum-xor-Prop P Q)

-- (c)
open import foundation.coproduct-types using
  ( is-prop-coproduct -- (P -> ¬ Q) → is-prop (P + Q)
  )
-- TODO: other direction

-- (d)
open import foundation.equality-coproduct-types using
  ( is-trunc-coproduct -- is-trunc (k+2) A → is-trunc (k+2) B → is-trunc (k+2) (A + B)
  )

open import elementary-number-theory.integers using
  ( is-set-ℤ)
```

**Exercise 12.5.** Diagonals of maps.

Note that the library calls "diagonals" the maps into the appropriate standard
pullback, i.e. it furthermore equips the pair with `refl : f x = f x`. The
book's diagonal is formalized as the "diagonal into the cartesian product".

```agda
open import foundation.diagonal-maps-cartesian-products-of-types using
  ( diagonal-product -- δ
  )

-- (a)
open import foundation.diagonal-maps-cartesian-products-of-types using
  ( is-prop-is-equiv-diagonal-product)

-- TODO: other direction; we have is-contr-map-diagonal-product-is-prop for
-- contractible maps

-- (b)
open import foundation.diagonal-maps-cartesian-products-of-types using
  ( is-equiv-eq-fiber-diagonal-product)

-- TODO: bundle it into an equivalence

-- (c)
open import foundation.diagonal-maps-cartesian-products-of-types using
  ( is-trunc-map-diagonal-product-is-trunc
  ; is-trunc-is-trunc-map-diagonal-product)

_ :
  {l1 : Level} {A : UU l1} (k : 𝕋) →
  is-trunc (succ-𝕋 k) A ↔ is-trunc-map k (diagonal-product A)
_ =
  λ k →
    is-trunc-map-diagonal-product-is-trunc k ,
    is-trunc-is-trunc-map-diagonal-product k
```

**Exercise 12.6.** Truncatedness of Σ-types.

```agda
-- (a)
open import foundation.truncated-types using
  ( is-trunc-Σ)
open import foundation.truncated-maps using
  ( is-trunc-fam-is-trunc-Σ)

_ :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (k : 𝕋) →
  is-trunc k A →
  ((x : A) → is-trunc k (B x)) ↔ is-trunc k (Σ A B)
_ =
  λ B k H → is-trunc-Σ H , is-trunc-fam-is-trunc-Σ k H

-- (b)
open import foundation.truncated-maps using
  ( is-trunc-map-is-trunc-domain-codomain)

-- TODO: put this somewhere else
-- actually it seems to be a pretty direct generalization of
-- is-trunc-is-trunc-map-into-is-trunc?
converse :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (k : 𝕋) →
  is-trunc k B → is-trunc-map k f → is-trunc k A
converse f neg-two-𝕋 H K =
  is-contr-is-equiv _ f (is-equiv-is-contr-map K) H
converse f (succ-𝕋 k) H K x y =
  converse (ap f) k
    ( H (f x) (f y))
    ( is-trunc-map-ap-is-trunc-map-succ k f K x y)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
  is-trunc k B →
  is-trunc k A ↔ is-trunc-map k f
_ =
  λ k f H →
    ( λ K → is-trunc-map-is-trunc-domain-codomain k K H) ,
    ( converse f k H)
```

**Exercise 12.7.** Truncatedness of cartesian product types.

Note that the backward implication is already implemented in greater generality
(for all `k : 𝕋`), which covers the second part of the exercise.

```agda
open import foundation.truncated-types using
  ( is-trunc-product'
  ; is-trunc-left-factor-product
  ; is-trunc-right-factor-product)

_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) →
  ((B → is-trunc (succ-𝕋 k) A) × (A → is-trunc (succ-𝕋 k) B)) ↔
  is-trunc (succ-𝕋 k) (A × B)
_ =
  λ k →
    ( λ (H , K) → is-trunc-product' k H K) ,
    ( λ H →
      is-trunc-left-factor-product (succ-𝕋 k) H ,
      is-trunc-right-factor-product (succ-𝕋 k) H)

-- TODO: conclusion
```

**Exercise 12.8.** Retracts of truncated types.

```agda
-- (a)
open import foundation.retracts-of-types using
  ( retract-eq)

-- (b)
open import foundation.truncated-types using
  ( is-trunc-retract-of)
```

**Exercise 12.9.** Concatenation of lists is 0-truncated.

TODO

**Exercise 12.10.** Truncatedness of the constant map.

```agda
open import foundation.constant-maps using
  ( is-trunc-map-point-is-trunc
  ; is-trunc-is-trunc-map-point)

_ :
  {l : Level} {A : UU l} (k : 𝕋) →
  is-trunc (succ-𝕋 k) A ↔ ((x : A) → is-trunc-map k (point x))
_ =
  λ k →
    is-trunc-map-point-is-trunc k ,
    is-trunc-is-trunc-map-point k
```

**Exercise 12.11.** Truncated maps in commuting triangles.

```agda
open import foundation.truncated-maps using
  ( is-trunc-map-top-map-triangle
  ; is-trunc-map-left-map-triangle)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f : A → X} {g : B → X} {h : A → B} (k : 𝕋) →
  coherence-triangle-maps f g h → is-trunc-map k g →
  is-trunc-map k f ↔ is-trunc-map k h
_ =
  λ k H K →
    is-trunc-map-top-map-triangle k _ _ _ H K ,
    is-trunc-map-left-map-triangle k _ _ _ H K
```

**Exercise 12.12.** Truncatedness of total maps.

```agda
open import foundation.functoriality-dependent-pair-types using
  ( is-trunc-map-tot
  ; is-trunc-map-is-trunc-map-tot)

_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3} (k : 𝕋) →
  (f : (x : A) → B x → C x) →
  ((x : A) → is-trunc-map k (f x)) ↔ is-trunc-map k (tot f)
_ =
  λ k f → is-trunc-map-tot k , is-trunc-map-is-trunc-map-tot k
```

**Exercise 12.13.** Truncatedness of the fiber inclusion.

```agda
open import foundation.fiber-inclusions using
  ( fiber-inclusion
  ; is-trunc-map-fiber-inclusion-is-trunc
  ; is-trunc-is-trunc-map-fiber-inclusion)

_ :
  {l1 l2 : Level} {A : UU l1} (k : 𝕋) →
  is-trunc (succ-𝕋 k) A ↔
  ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a))
_ =
  λ k →
    ( λ H B a → is-trunc-map-fiber-inclusion-is-trunc k B a H) ,
    ( is-trunc-is-trunc-map-fiber-inclusion k)
```

**Exercise 12.14.** Isolated elements.

Note that we call maps with decidable fibers _decidable maps_.

```agda
open import foundation.isolated-elements using
  ( is-isolated)
open import foundation.decidable-maps using
  ( is-decidable-map)

-- (a)
open import foundation.isolated-elements using
  ( is-decidable-point-is-isolated
  ; is-isolated-is-decidable-point)

_ :
  {l : Level} {A : UU l} (a : A) →
  is-isolated a ↔ is-decidable-map (point a)
_ =
  λ a → is-decidable-point-is-isolated a , is-isolated-is-decidable-point a

-- (b)
open import foundation.isolated-elements using
  ( is-prop-eq-isolated-element
  ; is-emb-point-is-isolated)
```

## 13 Function extensionality

### 13.1 Equivalent forms of function extensionality

**Proposition 13.1.1.** Equivalent forms of function extensionality.

Note that we only show the logical equivalence between `(i)` and `(iii)`.
TODO: do we care about adding `(ii)` to the chain?

```agda
open import foundation.function-extensionality using
  ( htpy-eq
  ; function-extensionality -- (i)
  )
open import foundation.homotopy-induction using ( is-torsorial-htpy -- (ii)
  ; induction-principle-homotopies -- (iii)
  ; induction-principle-homotopies-based-function-extensionality -- (i) → (iii)
  ; based-function-extensionality-induction-principle-homotopies -- (iii) → (i)
  )
```

**Theorem 13.1.2.** Weak function extensionality is equivalent to function
extensionality.

Note that we don't bundle the two implications into a logical equivalence,
because both principles quantify over universes, so they lie in `UUω`, and
`_↔_` doesn't handle large types.

TODO: report that there's a page break between the display math of "such and
such type" and "is contractible".

```agda
open import foundation.weak-function-extensionality using
  ( weak-function-extensionality
  ; weak-funext-funext
  ; funext-weak-funext)
```

**Axiom 13.1.3.** Function extensionality.

```agda
open import foundation.function-extensionality using
  ( funext
  ; eq-htpy)
```

**Theorem 13.1.5.** Dependent products preserve truncation level.

```agda
open import foundation.truncated-types using
  ( is-trunc-Π)
```

**Corollary 13.1.6.** The type of maps into a `k`-type is `k`-truncated.

```agda
open import foundation.truncated-types using
  ( is-trunc-function-type)
```

**Remark 13.1.7.** `¬ A` is a proposition for every `A`.

```agda
open import foundation.negation using
  ( is-prop-neg)
```

### 13.2 Identity systems on Π-types

**Theorem 13.2.1.** Type theoretic principle of choice.

Recall that the library has η for Σ types, so the identification
`(pr₁(h(x)), pr₂(h(x))) = h(x)` is satisfied by `refl` as well.

```agda
open import foundation.type-theoretic-principle-of-choice using
  ( map-distributive-Π-Σ -- "choice"
  ; map-inv-distributive-Π-Σ -- "choice⁻¹"
  ; is-equiv-map-distributive-Π-Σ)
```

**Corollary 13.2.2.** Distributivity of function types over Σ-types.

```agda
open import foundation.type-theoretic-principle-of-choice using
  ( equiv-mapping-into-Σ)
```

**Corollary 13.2.3.** Sections of `pr1` are sections of the type family.

```agda
open import foundation.sections using
  ( equiv-Π-section-pr1)
```

**Theorem 13.2.4.** Identity systems on Π-types.

TODO

### 13.3 Universal properties

**Theorem 13.3.1.** The universal property of Σ-types.

```agda
open import foundation.dependent-pair-types using
  ( ev-pair
  ; ind-Σ)
open import foundation.universal-property-dependent-pair-types using
  ( is-equiv-ev-pair)
```

**Theorem 13.3.3.** The universal property of identity types.

```agda
open import foundation.identity-types using
  ( ind-Id -- "ind-eq"
  )
open import foundation.universal-property-identity-types using
  ( ev-refl
  ; is-equiv-ev-refl)
```

### 13.4 Composing with equivalences

**Theorem 13.4.1.** The universal property of equivalences.

```agda
open import foundation.equivalences using
  ( is-equiv -- (i)
  )
open import foundation.dependent-universal-property-equivalences using
  ( dependent-universal-property-equiv -- (ii)
  ; is-equiv-precomp-Π-is-equiv -- (i) → (ii)
  )
open import foundation.universal-property-equivalences using
  ( universal-property-equiv -- (iii)
  ; is-equiv-precomp-is-equiv-precomp-Π -- (ii) → (iii)
  ; is-equiv-is-equiv-precomp -- (iii) → (i)
  )
```

### 13.5 The strong induction principle of ℕ

**Theorem 13.5.1.** Strong induction for the natural numbers.

```agda
open import elementary-number-theory.strong-induction-natural-numbers using
  ( strong-ind-ℕ
  ; compute-zero-strong-ind-ℕ
  ; compute-succ-strong-ind-ℕ
  ; □-≤-ℕ -- P ↦ P̃
  )
```

**Lemma 13.5.2.**

Note that we cannot state judgmental equalities as theorems, so that part needs
to be checked manually by verifying that `eq-zero-strong-ind-ℕ` is given by
`refl`.

```agda
open import elementary-number-theory.strong-induction-natural-numbers using
  ( zero-strong-ind-ℕ -- "p̃₀"
  ; eq-zero-strong-ind-ℕ -- p̃₀(0, p) = p₀
  )
```

**Lemma 13.5.3.**

```agda
open import elementary-number-theory.strong-induction-natural-numbers using
  ( succ-strong-ind-ℕ -- "p̃ₛ"
  ; htpy-succ-strong-ind-ℕ -- p̃ₛ(n, H, m, p) = H(m, q)
  ; eq-succ-strong-ind-ℕ -- p̃ₛ(n, H, n+1, p) = pₛ(n, H)
  )
```

### Exercises

**Exercise 13.1.** Inversion and concatenation of homotopies are equivalences.

```agda
open import foundation.homotopies using
  ( is-equiv-inv-htpy
  ; is-equiv-concat-htpy
  ; is-equiv-concat-htpy')
```

**Exercise 13.2.** Characterizing more identity types.

Note that the library provides two characterizations of identity types of
pointed maps: uniform pointed homotopies and non-uniform pointed homotopies.
See the respective files for the motivation.

```agda
-- (a)
open import structured-types.uniform-pointed-homotopies using
  ( uniform-pointed-htpy
  ; uniform-extensionality-pointed-Π)
open import structured-types.pointed-homotopies using
  ( pointed-htpy
  ; extensionality-pointed-map)

-- (b)
open import foundation.slice using
  ( htpy-hom-slice
  ; extensionality-hom-slice)

-- (c)
open import foundation.coslice using
  ( htpy-hom-coslice
  ; extensionality-hom-coslice)

-- (d)
open import foundation.homotopies-morphisms-arrows using
  ( htpy-hom-arrow
  ; extensionality-hom-arrow)
```

**Exercise 13.3.** Being truncated is a proposition.

Note on the naming: the proof of the fact that `is-contr(A)` is a proposition is
named `is-property-is-contr` instead of the perhaps expected `is-prop-is-contr`.
This is because the latter denotes the proof that `is-contr(A)` implies
`is-prop(A)`.

```agda
-- (a)
open import foundation.contractible-types using
  ( is-property-is-contr)

-- (b)
open import foundation.truncated-types using
  ( is-prop-is-trunc)
```

**Exercise 13.4.** Properties of equivalences.

Similarly to `is-property-is-contr`, the proof of the fact that being an
equivalence is a proposition is called `is-property-is-equiv`, since
`is-prop-is-equiv` denotes the proof that when `A` is equivalent to `B` and `B`
is a proposition, then `A` is a proposition.

```agda
-- (a)
open import foundation.equivalences using
  ( is-contr-section-is-equiv)

-- (b)
open import foundation.equivalences using
  ( is-contr-retraction-is-equiv)

-- (c)
open import foundation.equivalences using
  ( is-property-is-equiv)

-- (d)
open import foundation.equivalence-extensionality using
  ( extensionality-equiv)

-- (e)
open import foundation.truncated-types using
  ( is-trunc-equiv-is-trunc)
```

**Exercise 13.5.** Alternative (non-)notions of equivalences.

In `(a)` we construct the chain of equivalences
`is-path-split(f) ≃ is-equiv(f) ≃ is-coh-invertible(f)` instead, as `is-equiv`
is the primary notion of equivalences in the library.

```agda
-- (a)
open import foundation.path-split-maps using
  ( is-prop-is-path-split
  ; equiv-is-equiv-is-path-split -- is-path-split(f) ≃ is-equiv(f)
  )
open import foundation.coherently-invertible-maps using
  ( is-prop-is-coherently-invertible
  ; is-equiv-is-coherently-invertible-is-equiv)
_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f ≃ is-coherently-invertible f
_ = λ f → _ , is-equiv-is-coherently-invertible-is-equiv f

-- (b)
open import foundation.invertible-maps using
  ( is-equiv-is-invertible-id-htpy-id-id)
_ : {l : Level} {A : UU l} → (id {A = A} ~ id) ≃ is-invertible (id {A = A})
_ = _ , is-equiv-is-invertible-id-htpy-id-id _
```

**Exercise 13.6.** The universal property of empty types.

```agda
open import foundation.universal-property-empty-type using
  ( dependent-universal-property-empty -- (ii)
  ; dependent-universal-property-empty-is-empty -- (i) → (ii)
  ; universal-property-empty -- (iii)
  ; universal-property-dependent-universal-property-empty -- (ii) → (iii)
  ; is-empty-universal-property-empty -- (iii) → (i)
  )
```

**Exercise 13.7.** The universal property of contractible types.

Beware that the library defines the universal property as a property of a
morally pointed type, meaning that the type of the property is
`(A : 𝒰) (a : A) → 𝒱` rather than `(A : 𝒰) → 𝒱`. We also break the chain of
equivalences into two smaller ones.

```agda
open import foundation.universal-property-contractible-types using
  ( dependent-universal-property-contr -- (ii)
  ; dependent-universal-property-contr-is-contr -- (i) → (ii)
  ; universal-property-contr -- (iii)
  ; universal-property-dependent-universal-property-contr -- (ii) → (iii)
  -- (iii) → (iv) by instantiation
  ; is-contr-is-equiv-ev-point -- (iv) → (i)
  )
open import foundation.contractible-types using
  ( is-equiv-diagonal-exponential-is-contr -- (i) → (v)
  -- (v) → (vi) by instantiation
  ; is-contr-is-equiv-self-diagonal-exponential -- (vi) → i
  )
```

**Exercise 13.8.** The universal property of coproducts.

Note that here the universal properties are not statements but proofs of the
statements for the canonical inductive type `A + B`.

```agda
open import foundation.universal-property-coproduct-types using
  ( dependent-universal-property-coproduct
  ; universal-property-coproduct)
```

**Exercise 13.9.**

TODO. Note that `ev_b` is a less dependent version of `ev-refl-identity-system`,
which allows `C` to depend on `B` (and this lack of dependency is probably
compensated for by requiring the evaluation map to be an equivalence instead of
just having a section).

**Exercise 13.10.** The universal property of ℕ.

```agda
open import elementary-number-theory.universal-property-natural-numbers using
  ( is-contr-structure-preserving-map-ℕ)
```

**Exercise 13.11.** Ordinal induction on ℕ.

TODO the computation rule.

```agda
open import elementary-number-theory.ordinal-induction-natural-numbers using
  ( ordinal-ind-ℕ)
```

**Exercise 13.12.** Postcomposition by truncated maps.

```agda
-- (a)
open import foundation.functoriality-dependent-function-types using
  ( is-trunc-map-map-Π)

-- (b)
open import foundation.functoriality-dependent-function-types using
  ( is-equiv-map-equiv-Π)

-- (c)
open import foundation.functoriality-dependent-function-types using
  ( is-trunc-map-map-Π' -- (i) → (ii)
  ; is-trunc-map-is-trunc-map-map-Π' -- (ii) → (i)
  )

-- (d)
open import foundation.functoriality-function-types using
  ( is-trunc-map-postcomp-is-trunc-map -- (i) → (ii)
  ; is-trunc-map-is-trunc-map-postcomp -- (ii) → (i)
  ; is-emb-postcomp-is-emb
  ; is-emb-is-emb-postcomp
  )
-- special cases
open import foundation.postcomposition-functions using
  ( is-equiv-postcomp-is-equiv
  ; is-equiv-is-equiv-postcomp)
open import foundation.functoriality-function-types using
  ( is-emb-postcomp-is-emb
  ; is-emb-is-emb-postcomp)
```

**Exercise 13.13.** Π-types distribute over coproducts.

```agda
open import foundation.dependent-binomial-theorem using
  ( distributive-Π-coproduct)
```

**Exercise 13.14.** Retracts of sections.

TODO: `(b)` says that `retr(h) retract-of sec(f)` instead of `retr(f)`.

```agda
-- (a)
open import foundation.sections using
  ( section-left-factor-retract-of-section-composition)

-- (b)
open import foundation.retractions using
  ( retraction-right-factor-retract-of-retraction-left-factor)
```

**Exercise 13.15.** Maps over as maps of fibers.

To justify the naming choices in the library, for `(a)` we define the type of
lifts of a type family `P` over `X` agains a map `f : A → X` to be
`(a : A) → P(f a)`, and in this context the exercise asks us to show that `fib`
is the initial type family with a lift.

```agda
open import foundation.slice using
  ( hom-slice)

-- (a)
open import foundation.universal-property-family-of-fibers-of-maps using
  ( universal-property-family-of-fibers-fiber
  ; equiv-universal-property-family-of-fibers)

-- (b)
open import foundation.slice using
  ( fiberwise-hom -- codomain of α
  ; equiv-fiberwise-hom-hom-slice -- "α"
  )

-- TODO: move this
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  γ : fiberwise-hom f g ≃ ((a : A) → fiber g (f a))
  γ = equiv-universal-property-family-of-fibers f (fiber g)

  β : hom-slice f g → ((a : A) → fiber g (f a))
  β = λ H a → pr1 H a , inv (pr2 H a)

  _ : is-equiv β
  _ =
    is-equiv-is-invertible
      ( λ h → (λ a → pr1 (h a)) , (λ a → inv (pr2 (h a))))
      ( λ h → eq-htpy (λ a → eq-pair-Σ refl (inv-inv _)))
      ( λ x → eq-pair-Σ refl (eq-htpy (λ a → inv-inv _)))
    where
    open import foundation.equivalences using (is-equiv-is-invertible)
    open import foundation.identity-types using (inv-inv)

  _ : map-equiv γ ∘ map-equiv (equiv-fiberwise-hom-hom-slice f g) ~ β
  _ = refl-htpy

-- (c)
open import foundation.slice using
  ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice -- (i) → (ii)
  ; is-fiberwise-equiv-fiberwise-equiv-equiv-slice -- (ii) → (i)
  -- TODO (iii)
  ; equiv-fam-equiv-equiv-slice -- conclusion
  )
```

**Exercise 13.16.** Isomorphisms between sets.

```agda
open import foundation.isomorphisms-of-sets using
  ( equiv-iso-equiv-Set)
```

**Exercise 13.17.** Contractible sections of families over discrete types.

TODO.

**Exercise 13.18.** Retracts as sequential limits.

Following the naming conventions of the library, this exercise shows that `A` is
the sequential limit

```text
            f      f      f
  A ---> ⋯ ---> X ---> ⋯ ---> X.
```

Note that `f` is a split idempotent (as `f ∘ f ≐ i ∘ (r ∘ i) ∘ r ~ i ∘ r ≐ f`),
so this formalization should go there.

TODO.
