# Wiedijk's 100 Theorems

This file records formalized results from
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s
[_Formalizing 100 Theorems_](https://www.cs.ru.nl/~freek/100/)
{{#cite 100theorems}}.

```agda
module literature.100-theorems where
```

## The list

### 3. The denumerability of the rational numbers {#3}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import elementary-number-theory.rational-numbers using
  ( is-countable-ℚ)
```

### 4. The Pythagorean Theorem

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import linear-algebra.pythagorean-theorem-real-inner-product-spaces using
  ( pythagorean-theorem-ℝ-Inner-Product-Space)
```

### 11. The infinitude of primes {#11}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( infinitude-of-primes-ℕ)
```

### 25. Schröder–Bernstein theorem {#25}

**Author:** [Elif Uskuplu](https://elifuskuplu.github.io)

```agda
open import foundation.cantor-schroder-bernstein-escardo using
  ( Cantor-Schröder-Bernstein-Escardó ;
    Cantor-Schröder-Bernstein)
```

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import foundation.cantor-schroder-bernstein-decidable-embeddings using
  ( Cantor-Schröder-Bernstein-WLPO)
```

### 34. Divergence of the Harmonic Series {#34}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import elementary-number-theory.harmonic-series-rational-numbers using
  ( grows-without-bound-harmonic-series-ℚ)
```

### 42. Sum of the Reciprocals of the Triangular Numbers {#42}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import elementary-number-theory.triangular-numbers using
  ( sum-reciprocal-triangular-number-ℕ)
```

### 44. The binomial theorem {#44}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import commutative-algebra.binomial-theorem-commutative-rings using
  ( binomial-theorem-Commutative-Ring)
open import commutative-algebra.binomial-theorem-commutative-semirings using
  ( binomial-theorem-Commutative-Semiring)
open import ring-theory.binomial-theorem-rings using
  ( binomial-theorem-Ring)
open import ring-theory.binomial-theorem-semirings using
  ( binomial-theorem-Semiring)
open import elementary-number-theory.binomial-theorem-integers using
  ( binomial-theorem-ℤ)
open import elementary-number-theory.binomial-theorem-natural-numbers using
  ( binomial-theorem-ℕ)
```

### 52. The number of subsets of a set {#52}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import univalent-combinatorics.decidable-subtypes using
  ( number-of-elements-decidable-subtype-is-finite)
```

### 58. Formula for the number of combinations {#58}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import univalent-combinatorics.binomial-types using
  ( has-cardinality-binomial-type)
```

### 60. Bezout's lemma {#60}

**Author:** [Bryan Lu](https://blu-bird.github.io)

Note that the 60th theorem in Freek's list is listed as "Bezout's Theorem",
while the linked theorems are formalizations of Bezout's lemma, even though
these are different statements.

```agda
open import elementary-number-theory.bezouts-lemma-integers using
  ( bezouts-lemma-ℤ)
open import elementary-number-theory.bezouts-lemma-natural-numbers using
  ( bezouts-lemma-ℕ)
```

### 63. Cantor's theorem {#63}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import foundation.cantors-theorem using
  ( theorem-Cantor)
```

### 66. Sum of a Geometric Series {#66}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import real-numbers.geometric-sequences-real-numbers using
  ( compute-sum-standard-geometric-fin-sequence-ℝ ;
    compute-sum-standard-geometric-series-ℝ)
```

### 68. Sum of an arithmetic series {#68}

**Author:** [malarbol](http://www.github.com/malarbol)

```agda
open import elementary-number-theory.triangular-numbers using
  ( compute-triangular-number-ℕ)
open import ring-theory.arithmetic-series-semirings using
  ( compute-sum-add-mul-nat-Semiring)
```

### 69. Greatest common divisor algorithm {#69}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import
  elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( GCD-ℕ)
```

### 74. The principle of mathematical induction {#74}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import elementary-number-theory.natural-numbers using
  ( ind-ℕ)
```

### 78. The Cauchy-Schwarz inequality {#78}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import linear-algebra.cauchy-schwarz-inequality-real-inner-product-spaces using
  ( cauchy-schwarz-inequality-ℝ-Inner-Product-Space)
```

### 80. The fundamental theorem of arithmetic {#80}

**Author:** [Victor Blanchi](https://github.com/VictorBlanchi)

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( fundamental-theorem-arithmetic-list-ℕ)
```

### 91. The triangle inequality {#91}

**Author:** [malarbol](https://github.com/malarbol)

```agda
open import real-numbers.metric-space-of-real-numbers using
  ( is-triangular-neighborhood-ℝ)
```

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import real-numbers.absolute-value-real-numbers using
  ( triangle-inequality-abs-ℝ)
open import real-numbers.distance-real-numbers using
  ( triangle-inequality-dist-ℝ)
```

## See also

- The spiritual successor to _Formalizing 100 Theorems_ is _1000+ theorems_
  {{#cite 1000+theorems}}.

## References

{{#bibliography}}
