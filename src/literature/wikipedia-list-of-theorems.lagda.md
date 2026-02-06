# Wikipedia's list of theorems

On this page, we record formalized results in the agda-unimath library that are
on Wikipedia's
[list of theorems](https://en.wikipedia.org/wiki/List_of_theorems) or have a
Wikidata entry listed as an instance of a
[theorem](https://www.wikidata.org/wiki/Q65943). Additions to this list are very
welcome!

```agda
module literature.wikipedia-list-of-theorems where
```

## Formalized theorems

The theorems are ordered alphabetically, omitting leading definite articles
("the").

### Absolute convergence theorem

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import analysis.absolute-convergence-series-real-numbers using
  ( is-convergent-is-absolutely-convergent-series-ℝ)
open import functional-analysis.absolute-convergence-series-real-banach-spaces using
  ( is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space)
```

### Bézout's lemma {#Q513028}

**Author:** [Bryan Lu](https://blu-bird.github.io)

```agda
open import elementary-number-theory.bezouts-lemma-integers using
  ( bezouts-lemma-ℤ)
open import elementary-number-theory.bezouts-lemma-natural-numbers using
  ( bezouts-lemma-ℕ)
```

### Binomial theorem {#Q26708}

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

### Cantor–Schröder–Bernstein theorem {#Q1033910}

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

### Cantor's theorem {#Q474881}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import foundation.cantors-theorem using
  ( theorem-Cantor)
```

### Cayley's theorem {#Q179208}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import group-theory.cayleys-theorem using
  ( Cayleys-theorem)
```

### Cauchy-Schwarz inequality {#Q190546}

**Author:** [Louis Wasserman](https://github.com/lowasser) and
[malarbol](http://www.github.com/malarbol)

```agda
open import linear-algebra.cauchy-schwarz-inequality-real-inner-product-spaces using
  ( cauchy-schwarz-inequality-ℝ-Inner-Product-Space)
```

### Diaconescu's theorem {#Q3527059}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import foundation.diaconescus-theorem using
  ( theorem-Diaconescu)
```

### Euclid's theorem {#Q1506253}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( infinitude-of-primes-ℕ)
```

### Fundamental theorem of arithmetic {#Q670235}

**Author:** [Victor Blanchi](https://github.com/VictorBlanchi)

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( fundamental-theorem-arithmetic-list-ℕ)
```

### Fundamental theorem of equivalence relations

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import foundation.fundamental-theorem-of-equivalence-relations using
  ( equiv-equivalence-relation-partition)
```

### Fundamental theorem on homomorphisms {#Q1187646}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import group-theory.quotient-groups using
  ( is-quotient-group-quotient-Group)
```

### Intermediate Value Theorem {#Q245098}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import analysis.intermediate-value-theorem using
  ( intermediate-value-theorem-ℝ)
open import analysis.constructive-intermediate-value-theorem using
  ( constructive-intermediate-value-theorem-ℝ)
```

### Kleene's fixed point theorem {#Q3527263}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import domain-theory.kleenes-fixed-point-theorem-posets using
  ( is-least-fixed-point-theorem-kleene-hom-Poset ;
    is-least-fixed-point-theorem-kleene-Poset)
open import domain-theory.kleenes-fixed-point-theorem-omega-complete-posets using
  ( is-least-fixed-point-theorem-kleene-hom-ω-Complete-Poset ;
    is-least-fixed-point-theorem-kleene-ω-Complete-Poset)
```

### Knaster–Tarski fixed point theorem {#Q609612}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import order-theory.knaster-tarski-fixed-point-theorem using
  ( least-fixed-point-knaster-tarski-Inflattice ;
    greatest-fixed-point-knaster-tarski-Suplattice)
```

### Lawvere's fixed point theorem {#Q15809744}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import foundation.lawveres-fixed-point-theorem using
  ( fixed-point-theorem-Lawvere)
```

### Triangle inequality theorem {#Q208216}

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

### Pythagorean theorem {#Q11518}

**Author:** [Louis Wasserman](https://github.com/lowasser)

```agda
open import linear-algebra.orthogonality-real-inner-product-spaces using
  ( pythagorean-theorem-ℝ-Inner-Product-Space)
```

### Uniform limit theorem {#Q7885107}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import metric-spaces.uniform-limit-theorem-metric-spaces using
  ( is-pointwise-ε-δ-continuous-map-is-uniform-limit-sequence-pointwise-continuous-map-Metric-Space
  ; is-pointwise-continuous-map-is-uniform-limit-sequence-ACℕ-Metric-Space)
```

### Yoneda lemma {#Q320577}

**Author:** [Emily Riehl](https://emilyriehl.github.io/)

```agda
open import category-theory.yoneda-lemma-categories using
  ( lemma-yoneda-Category)
open import category-theory.yoneda-lemma-precategories using
  ( lemma-yoneda-Precategory)
```

## External links

- [List of theorems](https://en.wikipedia.org/wiki/List_of_theorems) on
  Wikipedia
- The [1000plus project](https://github.com/1000-plus)'s
  [_1000+ theorems_](https://1000-plus.github.io/) aims to record formalized
  results from Wikipedia's list of theorems in the 6 proof assistants Isabelle,
  HOL Light, Coq/Rocq, Lean, Metamath, and Mizar.
