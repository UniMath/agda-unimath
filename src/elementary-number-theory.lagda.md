# Elementary number theory

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the elementary number theory namespace

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory
  (funext : function-extensionality)
  where

open import elementary-number-theory.absolute-value-integers funext public
open import elementary-number-theory.ackermann-function public
open import elementary-number-theory.addition-integer-fractions funext public
open import elementary-number-theory.addition-integers funext public
open import elementary-number-theory.addition-natural-numbers public
open import elementary-number-theory.addition-positive-and-negative-integers funext public
open import elementary-number-theory.addition-rational-numbers funext public
open import elementary-number-theory.additive-group-of-rational-numbers funext public
open import elementary-number-theory.archimedean-property-integer-fractions funext public
open import elementary-number-theory.archimedean-property-integers funext public
open import elementary-number-theory.archimedean-property-natural-numbers funext public
open import elementary-number-theory.archimedean-property-positive-rational-numbers funext public
open import elementary-number-theory.archimedean-property-rational-numbers funext public
open import elementary-number-theory.arithmetic-functions funext public
open import elementary-number-theory.based-induction-natural-numbers funext public
open import elementary-number-theory.based-strong-induction-natural-numbers funext public
open import elementary-number-theory.bell-numbers funext public
open import elementary-number-theory.bezouts-lemma-integers funext public
open import elementary-number-theory.bezouts-lemma-natural-numbers funext public
open import elementary-number-theory.binomial-coefficients funext public
open import elementary-number-theory.binomial-theorem-integers funext public
open import elementary-number-theory.binomial-theorem-natural-numbers funext public
open import elementary-number-theory.bounded-sums-arithmetic-functions funext public
open import elementary-number-theory.catalan-numbers funext public
open import elementary-number-theory.cofibonacci funext public
open import elementary-number-theory.collatz-bijection funext public
open import elementary-number-theory.collatz-conjecture funext public
open import elementary-number-theory.commutative-semiring-of-natural-numbers funext public
open import elementary-number-theory.conatural-numbers funext public
open import elementary-number-theory.congruence-integers funext public
open import elementary-number-theory.congruence-natural-numbers funext public
open import elementary-number-theory.cross-multiplication-difference-integer-fractions funext public
open import elementary-number-theory.cubes-natural-numbers funext public
open import elementary-number-theory.decidable-dependent-function-types funext public
open import elementary-number-theory.decidable-total-order-integers funext public
open import elementary-number-theory.decidable-total-order-natural-numbers funext public
open import elementary-number-theory.decidable-total-order-rational-numbers funext public
open import elementary-number-theory.decidable-total-order-standard-finite-types funext public
open import elementary-number-theory.decidable-types funext public
open import elementary-number-theory.difference-integers funext public
open import elementary-number-theory.difference-rational-numbers funext public
open import elementary-number-theory.dirichlet-convolution funext public
open import elementary-number-theory.distance-integers funext public
open import elementary-number-theory.distance-natural-numbers funext public
open import elementary-number-theory.divisibility-integers funext public
open import elementary-number-theory.divisibility-modular-arithmetic funext public
open import elementary-number-theory.divisibility-natural-numbers funext public
open import elementary-number-theory.divisibility-standard-finite-types funext public
open import elementary-number-theory.equality-conatural-numbers funext public
open import elementary-number-theory.equality-integers funext public
open import elementary-number-theory.equality-natural-numbers funext public
open import elementary-number-theory.equality-rational-numbers funext public
open import elementary-number-theory.euclid-mullin-sequence funext public
open import elementary-number-theory.euclidean-division-natural-numbers funext public
open import elementary-number-theory.eulers-totient-function funext public
open import elementary-number-theory.exponentiation-natural-numbers funext public
open import elementary-number-theory.factorials funext public
open import elementary-number-theory.falling-factorials public
open import elementary-number-theory.fermat-numbers funext public
open import elementary-number-theory.fibonacci-sequence funext public
open import elementary-number-theory.field-of-rational-numbers funext public
open import elementary-number-theory.finitary-natural-numbers funext public
open import elementary-number-theory.finitely-cyclic-maps funext public
open import elementary-number-theory.fundamental-theorem-of-arithmetic funext public
open import elementary-number-theory.goldbach-conjecture funext public
open import elementary-number-theory.greatest-common-divisor-integers funext public
open import elementary-number-theory.greatest-common-divisor-natural-numbers funext public
open import elementary-number-theory.group-of-integers funext public
open import elementary-number-theory.half-integers funext public
open import elementary-number-theory.hardy-ramanujan-number funext public
open import elementary-number-theory.inclusion-natural-numbers-conatural-numbers funext public
open import elementary-number-theory.inequality-conatural-numbers funext public
open import elementary-number-theory.inequality-integer-fractions funext public
open import elementary-number-theory.inequality-integers funext public
open import elementary-number-theory.inequality-natural-numbers funext public
open import elementary-number-theory.inequality-rational-numbers funext public
open import elementary-number-theory.inequality-standard-finite-types funext public
open import elementary-number-theory.infinite-conatural-numbers funext public
open import elementary-number-theory.infinitude-of-primes funext public
open import elementary-number-theory.initial-segments-natural-numbers funext public
open import elementary-number-theory.integer-fractions funext public
open import elementary-number-theory.integer-partitions public
open import elementary-number-theory.integers public
open import elementary-number-theory.jacobi-symbol funext public
open import elementary-number-theory.kolakoski-sequence funext public
open import elementary-number-theory.legendre-symbol funext public
open import elementary-number-theory.lower-bounds-natural-numbers funext public
open import elementary-number-theory.maximum-natural-numbers funext public
open import elementary-number-theory.maximum-standard-finite-types funext public
open import elementary-number-theory.mediant-integer-fractions funext public
open import elementary-number-theory.mersenne-primes funext public
open import elementary-number-theory.minimum-natural-numbers funext public
open import elementary-number-theory.minimum-standard-finite-types funext public
open import elementary-number-theory.modular-arithmetic funext public
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext public
open import elementary-number-theory.monoid-of-natural-numbers-with-addition funext public
open import elementary-number-theory.monoid-of-natural-numbers-with-maximum funext public
open import elementary-number-theory.multiplication-integer-fractions funext public
open import elementary-number-theory.multiplication-integers funext public
open import elementary-number-theory.multiplication-lists-of-natural-numbers funext public
open import elementary-number-theory.multiplication-natural-numbers public
open import elementary-number-theory.multiplication-positive-and-negative-integers funext public
open import elementary-number-theory.multiplication-rational-numbers funext public
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers funext public
open import elementary-number-theory.multiplicative-group-of-rational-numbers funext public
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions funext public
open import elementary-number-theory.multiplicative-monoid-of-natural-numbers funext public
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers funext public
open import elementary-number-theory.multiplicative-units-integers public
open import elementary-number-theory.multiplicative-units-standard-cyclic-rings public
open import elementary-number-theory.multiset-coefficients public
open import elementary-number-theory.natural-numbers public
open import elementary-number-theory.negative-integers funext public
open import elementary-number-theory.nonnegative-integers funext public
open import elementary-number-theory.nonpositive-integers funext public
open import elementary-number-theory.nonzero-integers funext public
open import elementary-number-theory.nonzero-natural-numbers funext public
open import elementary-number-theory.nonzero-rational-numbers funext public
open import elementary-number-theory.ordinal-induction-natural-numbers funext public
open import elementary-number-theory.parity-natural-numbers funext public
open import elementary-number-theory.peano-arithmetic funext public
open import elementary-number-theory.pisano-periods funext public
open import elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility funext public
open import elementary-number-theory.positive-and-negative-integers funext public
open import elementary-number-theory.positive-conatural-numbers funext public
open import elementary-number-theory.positive-integer-fractions funext public
open import elementary-number-theory.positive-integers funext public
open import elementary-number-theory.positive-rational-numbers funext public
open import elementary-number-theory.powers-integers funext public
open import elementary-number-theory.powers-of-two funext public
open import elementary-number-theory.prime-numbers funext public
open import elementary-number-theory.products-of-natural-numbers funext public
open import elementary-number-theory.proper-divisors-natural-numbers funext public
open import elementary-number-theory.pythagorean-triples funext public
open import elementary-number-theory.rational-numbers funext public
open import elementary-number-theory.reduced-integer-fractions funext public
open import elementary-number-theory.relatively-prime-integers funext public
open import elementary-number-theory.relatively-prime-natural-numbers funext public
open import elementary-number-theory.repeating-element-standard-finite-type funext public
open import elementary-number-theory.retracts-of-natural-numbers funext public
open import elementary-number-theory.ring-of-integers funext public
open import elementary-number-theory.ring-of-rational-numbers funext public
open import elementary-number-theory.sieve-of-eratosthenes funext public
open import elementary-number-theory.square-free-natural-numbers funext public
open import elementary-number-theory.squares-integers funext public
open import elementary-number-theory.squares-modular-arithmetic funext public
open import elementary-number-theory.squares-natural-numbers funext public
open import elementary-number-theory.standard-cyclic-groups funext public
open import elementary-number-theory.standard-cyclic-rings funext public
open import elementary-number-theory.stirling-numbers-of-the-second-kind public
open import elementary-number-theory.strict-inequality-integer-fractions funext public
open import elementary-number-theory.strict-inequality-integers funext public
open import elementary-number-theory.strict-inequality-natural-numbers funext public
open import elementary-number-theory.strict-inequality-rational-numbers funext public
open import elementary-number-theory.strict-inequality-standard-finite-types funext public
open import elementary-number-theory.strictly-ordered-pairs-of-natural-numbers funext public
open import elementary-number-theory.strong-induction-natural-numbers funext public
open import elementary-number-theory.sums-of-natural-numbers funext public
open import elementary-number-theory.sylvesters-sequence funext public
open import elementary-number-theory.taxicab-numbers funext public
open import elementary-number-theory.telephone-numbers public
open import elementary-number-theory.triangular-numbers public
open import elementary-number-theory.twin-prime-conjecture funext public
open import elementary-number-theory.type-arithmetic-natural-numbers funext public
open import elementary-number-theory.unit-elements-standard-finite-types funext public
open import elementary-number-theory.unit-fractions-rational-numbers funext public
open import elementary-number-theory.unit-similarity-standard-finite-types funext public
open import elementary-number-theory.universal-property-conatural-numbers funext public
open import elementary-number-theory.universal-property-integers funext public
open import elementary-number-theory.universal-property-natural-numbers funext public
open import elementary-number-theory.upper-bounds-natural-numbers funext public
open import elementary-number-theory.well-ordering-principle-natural-numbers funext public
open import elementary-number-theory.well-ordering-principle-standard-finite-types funext public
open import elementary-number-theory.zero-conatural-numbers funext public
```
