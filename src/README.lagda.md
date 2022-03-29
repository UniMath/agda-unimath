# Univalent mathematics in Agda

Welcome to the website of the `agda-unimath` formalization project.

[![build](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml)

```agda
{-# OPTIONS --without-K --exact-split #-}
```

## Category theory

```agda
open import category-theory
open import category-theory.adjunctions-large-precategories
open import category-theory.anafunctors
open import category-theory.categories
open import category-theory.equivalences-categories
open import category-theory.equivalences-large-precategories
open import category-theory.equivalences-precategories
open import category-theory.functors-categories
open import category-theory.functors-large-precategories
open import category-theory.functors-precategories
open import category-theory.homotopies-natural-transformations-large-precategories
open import category-theory.initial-objects-precategories
open import category-theory.isomorphisms-categories
open import category-theory.isomorphisms-large-precategories
open import category-theory.isomorphisms-precategories
open import category-theory.large-categories
open import category-theory.large-precategories
open import category-theory.monomorphisms-large-precategories
open import category-theory.natural-isomorphisms-categories
open import category-theory.natural-isomorphisms-large-precategories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.natural-transformations-categories
open import category-theory.natural-transformations-large-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories
open import category-theory.slice-precategories
open import category-theory.terminal-objects-precategories
```

## Elementary number theory

```agda
open import elementary-number-theory
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.arithmetic-functions
open import elementary-number-theory.binomial-coefficients
open import elementary-number-theory.bounded-sums-arithmetic-functions
open import elementary-number-theory.catalan-numbers
open import elementary-number-theory.collatz-bijection
open import elementary-number-theory.collatz-conjecture
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.decidable-dependent-function-types
open import elementary-number-theory.decidable-types
open import elementary-number-theory.difference-integers
open import elementary-number-theory.dirichlet-convolution
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.divisibility-modular-arithmetic
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.divisibility-standard-finite-types
open import elementary-number-theory.equality-integers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.eulers-totient-function
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.falling-factorials
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.finitary-natural-numbers
open import elementary-number-theory.finitely-cyclic-maps
open import elementary-number-theory.fractions
open import elementary-number-theory.goldbach-conjecture
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.groups-of-modular-arithmetic
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.infinitude-of-primes
open import elementary-number-theory.integers
open import elementary-number-theory.iterating-functions
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.mersenne-primes
open import elementary-number-theory.minimum-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.ordinal-induction-natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.repeating-element-standard-finite-type
open import elementary-number-theory.retracts-of-natural-numbers
open import elementary-number-theory.square-free-natural-numbers
open import elementary-number-theory.stirling-numbers-of-the-second-kind
open import elementary-number-theory.strong-induction-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers
open import elementary-number-theory.triangular-numbers
open import elementary-number-theory.telephone-numbers
open import elementary-number-theory.twin-prime-conjecture
open import elementary-number-theory.unit-elements-standard-finite-types
open import elementary-number-theory.unit-similarity-standard-finite-types
open import elementary-number-theory.universal-property-natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types
```

## Finite group theory

```agda
open import finite-group-theory
open import finite-group-theory.abstract-quaternion-group
open import finite-group-theory.concrete-quaternion-group
open import finite-group-theory.finite-groups
open import finite-group-theory.finite-monoids
open import finite-group-theory.finite-semigroups
open import finite-group-theory.groups-of-order-2
open import finite-group-theory.orbits-permutations
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.transpositions
```

## Foundation

```agda
open import foundation
open import foundation.0-maps
open import foundation.1-types
open import foundation.2-types
open import foundation.algebras-polynomial-endofunctors
open import foundation.automorphisms
open import foundation.axiom-of-choice
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.binary-relations
open import foundation.boolean-reflection
open import foundation.booleans
open import foundation.cantors-diagonal-argument
open import foundation.cartesian-product-types
open import foundation.choice-of-representatives-equivalence-relation
open import foundation.coherently-invertible-maps
open import foundation.commuting-squares
open import foundation.complements
open import foundation.conjunction
open import foundation.connected-components-universes
open import foundation.connected-components
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.coslice
open import foundation.decidable-dependent-function-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.disjunction
open import foundation.distributivity-of-dependent-functions-over-coproduct-types
open import foundation.distributivity-of-dependent-functions-over-dependent-pairs
open import foundation.double-negation
open import foundation.effective-maps-equivalence-relations
open import foundation.elementhood-relation-w-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.epimorphisms-with-respect-to-sets
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equivalence-classes
open import foundation.equivalence-induction
open import foundation.equivalence-relations
open import foundation.equivalences-maybe
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.extensional-w-types
open import foundation.faithful-maps
open import foundation.fiber-inclusions
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-set-quotients
open import foundation.functoriality-set-truncation
open import foundation.functoriality-w-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.global-choice
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.images
open import foundation.impredicative-encodings
open import foundation.indexed-w-types
open import foundation.induction-principle-propositional-truncation
open import foundation.induction-w-types
open import foundation.inequality-w-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.involutions
open import foundation.isolated-points
open import foundation.isomorphisms-of-sets
open import foundation.law-of-excluded-middle
open import foundation.lawveres-fixed-point-theorem
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.lower-types-w-types
open import foundation.maybe
open import foundation.mere-equality
open import foundation.mere-equivalences
open import foundation.monomorphisms
open import foundation.multisets
open import foundation.negation
open import foundation.non-contractible-types
open import foundation.path-algebra
open import foundation.path-split-maps
open import foundation.polynomial-endofunctors
open import foundation.propositional-extensionality
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.pullbacks
open import foundation.raising-universe-levels
open import foundation.ranks-of-elements-w-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.replacement
open import foundation.retractions
open import foundation.russells-paradox
open import foundation.sections
open import foundation.set-presented-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.singleton-induction
open import foundation.slice
open import foundation.small-maps
open import foundation.small-multisets
open import foundation.small-types
open import foundation.small-universes
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.structure
open import foundation.subterminal-types
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.surjective-maps
open import foundation.truncated-equality
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.uniqueness-image
open import foundation.uniqueness-set-quotients
open import foundation.uniqueness-set-truncations
open import foundation.uniqueness-truncation
open import foundation.unit-type
open import foundation.univalence-implies-function-extensionality
open import foundation.univalence
open import foundation.univalent-type-families
open import foundation.universal-multiset
open import foundation.universal-property-booleans
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-fiber-products
open import foundation.universal-property-identity-types
open import foundation.universal-property-image
open import foundation.universal-property-maybe
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universal-property-propositional-truncation
open import foundation.universal-property-pullbacks
open import foundation.universal-property-set-quotients
open import foundation.universal-property-set-truncation
open import foundation.universal-property-truncation
open import foundation.universal-property-unit-type
open import foundation.universe-levels
open import foundation.unordered-pairs
open import foundation.w-types
open import foundation.weak-function-extensionality
open import foundation.weakly-constant-maps
```

## Foundation Core

```agda
open import foundation-core.0-maps
open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.commuting-squares
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equality-fibers-of-maps
open import foundation-core.equivalence-induction
open import foundation-core.equivalences
open import foundation-core.faithful-maps
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.homotopies
open import foundation-core.identity-systems
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.negation
open import foundation-core.path-split-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.singleton-induction
open import foundation-core.subtype-identity-principle
open import foundation-core.subtypes
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.type-arithmetic-cartesian-product-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.univalence
open import foundation-core.universe-levels
```

## Graph theory

```agda
open import graph-theory
open import graph-theory.connected-undirected-graphs
open import graph-theory.directed-graphs
open import graph-theory.edge-coloured-undirected-graphs
open import graph-theory.equivalences-undirected-graphs
open import graph-theory.finite-graphs
open import graph-theory.incidence-undirected-graphs
open import graph-theory.matchings
open import graph-theory.mere-equivalences-undirected-graphs
open import graph-theory.morphisms-directed-graphs
open import graph-theory.morphisms-undirected-graphs
open import graph-theory.orientations-undirected-graphs
open import graph-theory.paths-undirected-graphs
open import graph-theory.polygons
open import graph-theory.reflexive-graphs
open import graph-theory.regular-undirected-graphs
open import graph-theory.simple-undirected-graphs
open import graph-theory.undirected-graphs
```

## Group theory

```agda
open import group-theory
open import group-theory.abelian-groups
open import group-theory.abelian-subgroups
open import group-theory.abstract-group-torsors
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.category-of-groups
open import group-theory.category-of-semigroups
open import group-theory.cayleys-theorem
open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.concrete-subgroups
open import group-theory.conjugation
open import group-theory.embeddings-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.equivalences-group-actions
open import group-theory.equivalences-semigroups
open import group-theory.examples-higher-groups
open import group-theory.furstenberg-groups
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.higher-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.invertible-elements-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.isomorphisms-group-actions
open import group-theory.isomorphisms-groups
open import group-theory.isomorphisms-semigroups
open import group-theory.mere-equivalences-group-actions
open import group-theory.monoids
open import group-theory.orbits-group-actions
open import group-theory.precategory-of-group-actions
open import group-theory.precategory-of-groups
open import group-theory.precategory-of-semigroups
open import group-theory.principal-group-actions
open import group-theory.semigroups
open import group-theory.sheargroups
open import group-theory.stabilizer-groups
open import group-theory.subgroups
open import group-theory.substitution-functor-group-actions
open import group-theory.symmetric-groups
open import group-theory.transitive-group-actions
```

## Linear algebra

```agda
open import linear-algebra
open import linear-algebra.constant-matrices
open import linear-algebra.constant-vectors
open import linear-algebra.diagonal-matrices-on-rings
open import linear-algebra.functoriality-matrices
open import linear-algebra.functoriality-vectors
open import linear-algebra.matrices-on-rings
open import linear-algebra.matrices
open import linear-algebra.multiplication-matrices
open import linear-algebra.scalar-multiplication-matrices
open import linear-algebra.scalar-multiplication-vectors
open import linear-algebra.transposition-matrices
open import linear-algebra.vectors-on-rings
open import linear-algebra.vectors
```

## Order theory

```agda
open import order-theory
open import order-theory.chains-posets
open import order-theory.chains-preorders
open import order-theory.decidable-subposets
open import order-theory.decidable-subpreorders
open import order-theory.finite-posets
open import order-theory.finite-preorders
open import order-theory.finitely-graded-posets
open import order-theory.greatest-lower-bounds-posets
open import order-theory.interval-subposets
open import order-theory.largest-elements-posets
open import order-theory.largest-elements-preorders
open import order-theory.least-elements-posets
open import order-theory.least-elements-preorders
open import order-theory.locally-finite-posets
open import order-theory.maximal-chains-posets
open import order-theory.maximal-chains-preorders
open import order-theory.meet-semilattices
open import order-theory.planar-binary-trees
open import order-theory.posets
open import order-theory.preorders
open import order-theory.subposets
open import order-theory.subpreorders
open import order-theory.total-posets
open import order-theory.total-preorders
```

## Polytopes

```agda
open import polytopes
open import polytopes.abstract-polytopes
```

## Ring theory

```agda
open import ring-theory
open import ring-theory.commutative-rings
open import ring-theory.discrete-fields
open import ring-theory.division-rings
open import ring-theory.eisenstein-integers
open import ring-theory.gaussian-integers
open import ring-theory.homomorphisms-commutative-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.ideals
open import ring-theory.invertible-elements-rings
open import ring-theory.isomorphisms-commutative-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.localizations-rings
open import ring-theory.nontrivial-rings
open import ring-theory.rings
```

## Synthetic homotopy theory

```agda
open import synthetic-homotopy-theory
open import synthetic-homotopy-theory.23-pullbacks
open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.25-cubical-diagrams
open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.26-id-pushout
open import synthetic-homotopy-theory.27-sequences
open import synthetic-homotopy-theory.circle
open import synthetic-homotopy-theory.commutative-operations
open import synthetic-homotopy-theory.cyclic-types
open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.groups-of-loops-in-1-types
open import synthetic-homotopy-theory.infinite-cyclic-types
open import synthetic-homotopy-theory.interval-type
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pointed-dependent-functions
open import synthetic-homotopy-theory.pointed-equivalences
open import synthetic-homotopy-theory.pointed-families-of-types
open import synthetic-homotopy-theory.pointed-homotopies
open import synthetic-homotopy-theory.pointed-maps
open import synthetic-homotopy-theory.pointed-types
open import synthetic-homotopy-theory.spaces
open import synthetic-homotopy-theory.triple-loop-spaces
open import synthetic-homotopy-theory.universal-cover-circle
```

## Tutorials

```agda
open import tutorials.basic-agda
```

## Univalent combinatorics

```agda
open import univalent-combinatorics
open import univalent-combinatorics.2-element-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.binomial-types
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-function-types
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.counting-fibers-of-maps
open import univalent-combinatorics.counting-function-types
open import univalent-combinatorics.counting-maybe
open import univalent-combinatorics.counting
open import univalent-combinatorics.cubes
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-product-finite-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.embeddings-standard-finite-types
open import univalent-combinatorics.embeddings
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.equivalences-cubes
open import univalent-combinatorics.equivalences-standard-finite-types
open import univalent-combinatorics.equivalences
open import univalent-combinatorics.fibers-of-maps-between-finite-types
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-connected-components
open import univalent-combinatorics.finite-function-types
open import univalent-combinatorics.finite-presentations
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.inequality-types-with-counting
open import univalent-combinatorics.injective-maps
open import univalent-combinatorics.lists
open import univalent-combinatorics.maybe
open import univalent-combinatorics.orientations-cubes
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.presented-pi-finite-types
open import univalent-combinatorics.ramsey-theory
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.species
open import univalent-combinatorics.standard-finite-pruned-trees
open import univalent-combinatorics.standard-finite-trees
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.sums-of-natural-numbers
open import univalent-combinatorics.surjective-maps
```

## Wild algebra

```agda
open import wild-algebra
open import wild-algebra.magmas
open import wild-algebra.universal-property-lists-wild-monoids
open import wild-algebra.wild-groups
open import wild-algebra.wild-monoids
open import wild-algebra.wild-unital-magmas
```

## Everything

See the list of all Agda modules [here](everything.html).

