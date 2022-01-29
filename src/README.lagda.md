---
title: Formalisation of the Symmetry Book
---

[![build](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml)


```agda
{-# OPTIONS --without-K --exact-split #-}
```

## Foundation

```agda
open import foundation.0-maps
open import foundation.1-types
open import foundation.2-types
open import foundation.binary-relations
open import foundation.boolean-reflection
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coherently-invertible-maps
open import foundation.commuting-squares
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.faithful-maps
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.isolated-points
open import foundation.lists
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.non-contractible-types
open import foundation.path-split-maps
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.singleton-induction
open import foundation.split-surjective-maps
open import foundation.subterminal-types
open import foundation.subtypes
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels
```

## Elementary number theory

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.classical-finite-types
open import elementary-number-theory.collatz-conjecture
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.divisibility-standard-finite-types
open import elementary-number-theory.equality-integers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.equality-standard-finite-types
open import elementary-number-theory.equivalences-standard-finite-types
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.finitary-natural-numbers
open import elementary-number-theory.finitely-cyclic-maps
open import elementary-number-theory.goldbach-conjecture
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.integers
open import elementary-number-theory.iterating-functions
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.standard-finite-types
open import elementary-number-theory.twin-prime-conjecture
open import elementary-number-theory.well-ordering-principle-natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types
```

## Univalent foundation

```agda
open import univalent-foundations.13-function-extensionality public
open import univalent-foundations.13-function-extensionality-solutions public
open import univalent-foundations.14-propositional-truncation public
open import univalent-foundations.15-image public
open import univalent-foundations.16-finite-types public
open import univalent-foundations.17-univalence public
open import univalent-foundations.18-set-quotients public
open import univalent-foundations.W-types public
open import univalent-foundations.pointed-types public
```

## Categories

```agda
open import categories.categories public
open import categories.functors public
open import categories.natural-transformations public
open import categories.large-categories public
open import categories.adjunctions public
```

## The circle

```agda
open import the-circle.the-circle public
open import the-circle.universal-cover public
open import the-circle.integers public
open import the-circle.cyclic-types public
open import the-circle.infinite-cyclic-types public
```

## Synthetic homotopy theory

```agda
open import synthetic-homotopy-theory.23-pullbacks public
open import synthetic-homotopy-theory.24-pushouts public
open import synthetic-homotopy-theory.25-cubical-diagrams public
open import synthetic-homotopy-theory.26-descent public
open import synthetic-homotopy-theory.26-id-pushout public
open import synthetic-homotopy-theory.27-sequences public
open import synthetic-homotopy-theory.spaces public
```

## Groups 

```agda
open import groups.abstract-groups public
open import groups.abstract-abelian-groups public
open import groups.abstract-group-actions public
open import groups.abstract-group-torsors public
open import groups.higher-groups public
open import groups.concrete-groups public
open import groups.examples-higher-groups public
open import groups.concrete-group-actions public
open import groups.sheargroups public
open import groups.furstenberg-groups public
```

## Subgroups

```agda
open import subgroups.abstract-subgroups public
open import subgroups.abstract-abelian-subgroups public
```

## Order theory

```agda
open import order-theory.preorders public
open import order-theory.finite-preorders public
open import order-theory.posets public
open import order-theory.finite-posets public
open import order-theory.finitely-graded-posets public
```

## Univalent combinatorics

```agda
open import univalent-combinatorics.unordered-pairs public
open import univalent-combinatorics.finite-graphs public
open import univalent-combinatorics.undirected-graphs public
open import univalent-combinatorics.directed-graphs public
open import univalent-combinatorics.reflexive-graphs public
open import univalent-combinatorics.polygons public
open import univalent-combinatorics.abstract-polytopes public
open import univalent-combinatorics.pi-finite-types public
open import univalent-combinatorics.finite-presentations public
open import univalent-combinatorics.ramsey-theory public
open import univalent-combinatorics.isolated-points public
open import univalent-combinatorics.quaternion-group public
```

## Rings

```agda
open import rings.rings public
open import rings.rings-with-properties public
open import rings.ideals public
open import rings.localizations-rings public
open import rings.eisenstein-integers public
open import rings.gaussian-integers public
```

## Everything

See the list of all Agda modules [here](everything.html).

