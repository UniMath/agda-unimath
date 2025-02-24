# 1000+ theorems

On this page, we record formalized results in the agda-unimath library following
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/) and
[collaborators](https://github.com/1000-plus)'
[_1000+ theorems_](https://1000-plus.github.io/) project
{{#cite 1000+theorems}}. This project records the formalization status of
theorems in mathematics that have their own Wikipedia entry. We welcome any
contribution to this list!

```agda
module literature.1000plus-theorems where
```

## Formalized theorems

The theorems are ordered alphabetically, omitting definite articles ("the").

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

**Note:** The formalization of the Cantor-Schröder-Bernstein theorem in
agda-unimath is a generalization of the statement to all types, i.e., it is not
restricted to sets. This generalization is originally due to Martin-Escardó,
hence we refer to the generalization as the Cantor-Schröder-Bernstein-Escardó
theorem.

```agda
open import foundation.cantor-schroder-bernstein-escardo using
  ( Cantor-Schröder-Bernstein-Escardó ;
    Cantor-Schröder-Bernstein)
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

### Yoneda lemma {#Q320577}

**Author:** [Emily Riehl](https://emilyriehl.github.io/)

```agda
open import category-theory.yoneda-lemma-categories using
  ( lemma-yoneda-Category)
open import category-theory.yoneda-lemma-precategories using
  ( lemma-yoneda-Precategory)
```

## See also

- The spiritual predecessor of _1000+ theorems_ is
  [_Formalizing 100 Theorems_](literature.100-theorems.md), also due to Freek
  Wiedijk {{#cite 100theorems}}.

## References

{{#bibliography}}

## External links

- [List of theorems](https://en.wikipedia.org/wiki/List_of_theorems) on
  Wikipedia
- [1000+ theorems](https://1000-plus.github.io/)
- [1000-plus](https://github.com/1000-plus/1000-plus.github.io) on GitHub
