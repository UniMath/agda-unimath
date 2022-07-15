---
title: Univalent mathematics in Agda
---

Welcome to the website of the `agda-unimath` formalization project.

[![CI](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml/badge.svg)](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml) [![pages-build-deployment](https://github.com/UniMath/agda-unimath/actions/workflows/pages/pages-build-deployment/badge.svg)](https://github.com/UniMath/agda-unimath/actions/workflows/pages/pages-build-deployment)

The `agda-unimath` library is a new formalisation project for univalent mathematics in Agda. Our goal is to formalize an extensive curriculum of mathematics from the univalent point of view. Furthermore, we think libraries of formalized mathematics have the potential to be useful, and informative resources for mathematicians. Our library is designed to work towards this goal, and we welcome contributions to the library about any topic in mathematics.

The library is built in Agda 2.6.2. It can be compiled by running `make check` from the main folder of the repository.

## Joining the project

Great, you want to contribute something! The best way to start is to find us in our chat channels on the [agda-unimath discord](https://discord.gg/Zp2e8hYsuX). We have a vibing community there, and you're more than welcome to join us just to hang out.

Once you've decided what you want to contribute, the best way to proceed is to make your own fork of the library. Within your fork, make a separate branch in which you will be making your contributions. Now you're ready to start your project! When you've completed your formalization you can proceed by making a pull request. Then we will review your contributions, and merge it when it is ready for the `agda-unimath` library.

## Statement of inclusion

There are many reasons to contribute something to a library of formalized mathematics. Some do it just for fun, some do it for their research, some do it to learn something. Whatever your reason is, we welcome your contributions! To keep the experience of contributing something to our library enjoyable for everyone, we strive for an inclusive community of contributors. You can expect from us that we are kind and respectful in discussions, that we will be mindful of your pronouns and use [inclusive language](https://www.apa.org/about/apa/equity-diversity-inclusion/language-guidelines), and that we value your input regardless of your level of experience or status in the community. We're commited to providing a safe and welcoming environment to people of any gender identity, sexual orientation, race, colour, age, ability, ethnicity, background, or fluency in English -- here on github, in online communication channels, and in person. Homotopy type theory is difficult enough without all the barriers that many of us have to face, so we hope to bring some of those down a bit.

:rainbow: Happy contributing!

Elisabeth Bonnevier
Jonathan Prieto-Cubides
Egbert Rijke

```agda
{-# OPTIONS --without-K --exact-split --guardedness #-}
```

See the list of all Agda modules [here](everything.html).

## Category theory

```agda
open import category-theory
open import category-theory.adjunctions-large-precategories
open import category-theory.anafunctors
open import category-theory.categories
open import category-theory.epimorphisms-large-precategories
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

## Commutative algebra

```agda
open import commutative-algebra
open import commutative-algebra.commutative-rings
open import commutative-algebra.discrete-fields
open import commutative-algebra.eisenstein-integers
open import commutative-algebra.gaussian-integers
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.integral-domains
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.isomorphisms-commutative-rings
open import commutative-algebra.local-commutative-rings
open import commutative-algebra.prime-ideals-commutative-rings
open import commutative-algebra.zariski-topology
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
open import elementary-number-theory.integer-partitions
open import elementary-number-theory.integers
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
open import elementary-number-theory.pythagorean-triples
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.repeating-element-standard-finite-type
open import elementary-number-theory.retracts-of-natural-numbers
open import elementary-number-theory.square-free-natural-numbers
open import elementary-number-theory.stirling-numbers-of-the-second-kind
open import elementary-number-theory.strong-induction-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers
open import elementary-number-theory.telephone-numbers
open import elementary-number-theory.triangular-numbers
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
open import finite-group-theory.alternating-groups
open import finite-group-theory.cartier-delooping-sign-homomorphism
open import finite-group-theory.concrete-quaternion-group
open import finite-group-theory.finite-groups
open import finite-group-theory.finite-monoids
open import finite-group-theory.finite-semigroups
open import finite-group-theory.groups-of-order-2
open import finite-group-theory.orbits-permutations
open import finite-group-theory.permutations
open import finite-group-theory.sign-homomorphism
open import finite-group-theory.simpson-delooping-sign-homomorphism
open import finite-group-theory.tetrahedra-in-3-space
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
open import foundation.bands
open import foundation.binary-embeddings
open import foundation.binary-equivalences-unordered-pairs-of-types
open import foundation.binary-equivalences
open import foundation.binary-operations-unordered-pairs-of-types
open import foundation.binary-relations
open import foundation.boolean-reflection
open import foundation.booleans
open import foundation.cantor-schroder-bernstein-escardo
open import foundation.cantors-diagonal-argument
open import foundation.cartesian-product-types
open import foundation.choice-of-representatives-equivalence-relation
open import foundation.coherently-invertible-maps
open import foundation.commutative-operations
open import foundation.commuting-squares
open import foundation.complements
open import foundation.cones-pullbacks
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
open import foundation.decidable-equivalence-relations
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-binomial-theorem
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.double-powersets
open import foundation.dubuc-penon-compact-types
open import foundation.effective-maps-equivalence-relations
open import foundation.elementhood-relation-w-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.endomorphisms
open import foundation.epimorphisms-with-respect-to-sets
open import foundation.equality-cartesian-product-types
open import foundation.equality-coproduct-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.equational-reasoning
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
open import foundation.hilberts-epsilon-operators
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-truncated-types
open import foundation.identity-types
open import foundation.images
open import foundation.impredicative-encodings
open import foundation.impredicative-universes
open import foundation.indexed-w-types
open import foundation.induction-principle-propositional-truncation
open import foundation.induction-w-types
open import foundation.inequality-w-types
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.intersection
open import foundation.involutions
open import foundation.isolated-points
open import foundation.isomorphisms-of-sets
open import foundation.iterating-automorphisms
open import foundation.iterating-functions
open import foundation.iterating-involutions
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
open import foundation.multisubsets
open import foundation.negation
open import foundation.non-contractible-types
open import foundation.pairs-of-distinct-elements
open import foundation.partial-elements
open import foundation.path-algebra
open import foundation.path-split-maps
open import foundation.polynomial-endofunctors
open import foundation.powersets
open import foundation.principle-of-omniscience
open import foundation.products-unordered-pairs-of-types
open import foundation.products-unordered-tuples-of-types
open import foundation.propositional-extensionality
open import foundation.propositional-maps
open import foundation.propositional-resizing
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.pullbacks
open import foundation.raising-universe-levels
open import foundation.ranks-of-elements-w-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.repetitions-sequences
open import foundation.repetitions
open import foundation.replacement
open import foundation.retractions
open import foundation.russells-paradox
open import foundation.sections
open import foundation.sequences
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
open import foundation.symmetric-difference
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
open import foundation.type-theoretic-principle-of-choice
open import foundation.union
open import foundation.unique-existence
open import foundation.uniqueness-image
open import foundation.uniqueness-set-quotients
open import foundation.uniqueness-set-truncations
open import foundation.uniqueness-truncation
open import foundation.unit-type
open import foundation.unital-binary-operations
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
open import foundation.unordered-pairs-of-types
open import foundation.unordered-pairs
open import foundation.unordered-tuples-of-types
open import foundation.unordered-tuples
open import foundation.w-types
open import foundation.weak-function-extensionality
open import foundation.weakly-constant-maps
open import foundation.xor
```

## Foundation Core

```agda
open import foundation-core.0-maps
open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.commuting-squares
open import foundation-core.cones-pullbacks
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
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.homotopies
open import foundation-core.identity-systems
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.negation
open import foundation-core.path-split-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
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
open import foundation-core.universal-property-pullbacks
open import foundation-core.universe-levels
```

## Graph theory

```agda
open import graph-theory
open import graph-theory.circuits-undirected-graphs
open import graph-theory.closed-walks-undirected-graphs
open import graph-theory.complete-bipartite-graphs
open import graph-theory.complete-multipartite-graphs
open import graph-theory.complete-undirected-graphs
open import graph-theory.connected-undirected-graphs
open import graph-theory.cycles-undirected-graphs
open import graph-theory.directed-graph-structures-on-standard-finite-sets
open import graph-theory.directed-graphs
open import graph-theory.edge-coloured-undirected-graphs
open import graph-theory.embeddings-undirected-graphs
open import graph-theory.equivalences-undirected-graphs
open import graph-theory.eulerian-circuits-undirected-graphs
open import graph-theory.faithful-morphisms-undirected-graphs
open import graph-theory.finite-graphs
open import graph-theory.hypergraphs
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
open import graph-theory.totally-faithful-morphisms-undirected-graphs
open import graph-theory.undirected-graph-structures-on-standard-finite-sets
open import graph-theory.undirected-graphs
open import graph-theory.vertex-covers
open import graph-theory.voltage-graphs
```

## Group theory

```agda
open import group-theory
open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.automorphism-groups
open import group-theory.cartesian-products-abelian-groups
open import group-theory.cartesian-products-groups
open import group-theory.cartesian-products-monoids
open import group-theory.cartesian-products-semigroups
open import group-theory.category-of-groups
open import group-theory.category-of-semigroups
open import group-theory.cayleys-theorem
open import group-theory.centers-groups
open import group-theory.commutative-monoids
open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.conjugation
open import group-theory.contravariant-pushforward-concrete-group-actions
open import group-theory.embeddings-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.epimorphisms-groups
open import group-theory.equivalences-concrete-group-actions
open import group-theory.equivalences-group-actions
open import group-theory.equivalences-semigroups
open import group-theory.fixed-points-higher-group-actions
open import group-theory.free-concrete-group-actions
open import group-theory.free-higher-group-actions
open import group-theory.furstenberg-groups
open import group-theory.group-actions
open import group-theory.groups
open import group-theory.higher-group-actions
open import group-theory.higher-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-concrete-group-actions
open import group-theory.homomorphisms-generated-subgroups
open import group-theory.homomorphisms-group-actions
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-higher-groups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.integers-higher-group
open import group-theory.inverse-semigroups
open import group-theory.invertible-elements-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.isomorphisms-group-actions
open import group-theory.isomorphisms-groups
open import group-theory.isomorphisms-semigroups
open import group-theory.loop-groups-sets
open import group-theory.kernels
open import group-theory.mere-equivalences-group-actions
open import group-theory.monoid-actions
open import group-theory.monoids
open import group-theory.monomorphisms-concrete-groups
open import group-theory.monomorphisms-groups
open import group-theory.normal-subgroups
open import group-theory.normal-subgroups-concrete-groups
open import group-theory.orbit-stabilizer-theorem-concrete-groups
open import group-theory.orbits-concrete-group-actions
open import group-theory.orbits-group-actions
open import group-theory.orbits-higher-group-actions
open import group-theory.orbits-monoid-actions
open import group-theory.precategory-of-group-actions
open import group-theory.precategory-of-groups
open import group-theory.precategory-of-semigroups
open import group-theory.principal-group-actions
open import group-theory.principal-torsors-concrete-groups
open import group-theory.products-of-tuples-of-elements-commutative-monoids
open import group-theory.semigroups
open import group-theory.sheargroups
open import group-theory.shriek-concrete-group-actions
open import group-theory.stabilizer-groups
open import group-theory.stabilizer-groups-concrete-group-actions
open import group-theory.subgroups
open import group-theory.subgroups-abelian-groups
open import group-theory.subgroups-concrete-groups
open import group-theory.subgroups-generated-by-subsets-groups
open import group-theory.subgroups-higher-groups
open import group-theory.substitution-functor-concrete-group-actions
open import group-theory.substitution-functor-group-actions
open import group-theory.symmetric-groups
open import group-theory.symmetric-higher-groups
open import group-theory.torsors
open import group-theory.transitive-concrete-group-actions
open import group-theory.transitive-group-actions
open import group-theory.unordered-tuples-of-elements-commutative-monoids
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
open import order-theory.distributive-lattices
open import order-theory.finite-posets
open import order-theory.finite-preorders
open import order-theory.finitely-graded-posets
open import order-theory.greatest-lower-bounds-posets
open import order-theory.interval-subposets
open import order-theory.join-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.largest-elements-posets
open import order-theory.largest-elements-preorders
open import order-theory.lattices
open import order-theory.least-elements-posets
open import order-theory.least-elements-preorders
open import order-theory.least-upper-bounds-posets
open import order-theory.locally-finite-posets
open import order-theory.maximal-chains-posets
open import order-theory.maximal-chains-preorders
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-posets
open import order-theory.order-preserving-maps-preorders
open import order-theory.planar-binary-trees
open import order-theory.posets
open import order-theory.preorders
open import order-theory.subposets
open import order-theory.subpreorders
open import order-theory.total-posets
open import order-theory.total-preorders
```

## Organic chemistry

```agda
open import organic-chemistry
open import organic-chemistry.alcohols
open import organic-chemistry.alkanes
open import organic-chemistry.alkenes
open import organic-chemistry.alkynes
open import organic-chemistry.hydrocarbons
open import organic-chemistry.saturated-carbons
```

## Polytopes

```agda
open import polytopes
open import polytopes.abstract-polytopes
```

## Ring theory

```agda
open import ring-theory
open import ring-theory.dependent-products-rings
open import ring-theory.division-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.ideals-generated-by-subsets-rings
open import ring-theory.ideals-rings
open import ring-theory.invariant-basis-property-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.local-rings
open import ring-theory.localizations-rings
open import ring-theory.modules-rings
open import ring-theory.nil-ideals-rings
open import ring-theory.nilpotent-elements-rings
open import ring-theory.nontrivial-rings
open import ring-theory.opposite-rings
open import ring-theory.powers-of-elements-rings
open import ring-theory.products-rings
open import ring-theory.radical-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

## Set theory

```agda
open import set-theory
open import set-theory.baire-space
open import set-theory.cantor-space
open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

## Structured types

```agda
open import structured-types
open import structured-types.coherent-h-spaces
open import structured-types.contractible-pointed-types
open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.faithful-pointed-maps
open import structured-types.finite-multiplication-magmas
open import structured-types.magmas
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.morphisms-coherent-h-spaces
open import structured-types.morphisms-magmas
open import structured-types.morphisms-types-equipped-with-endomorphisms
open import structured-types.pointed-dependent-functions
open import structured-types.pointed-equivalences
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-types-equipped-with-automorphisms
open import structured-types.types-equipped-with-automorphisms
open import structured-types.types-equipped-with-endomorphisms
open import structured-types.universal-property-lists-wild-monoids
open import structured-types.wild-groups
open import structured-types.wild-loops
open import structured-types.wild-monoids
open import structured-types.wild-quasigroups
open import structured-types.wild-semigroups
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
open import synthetic-homotopy-theory.cofibers
open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.groups-of-loops-in-1-types
open import synthetic-homotopy-theory.infinite-complex-projective-space
open import synthetic-homotopy-theory.infinite-cyclic-types
open import synthetic-homotopy-theory.interval-type
open import synthetic-homotopy-theory.iterated-loop-spaces
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.multiplication-circle
open import synthetic-homotopy-theory.prespectra
open import synthetic-homotopy-theory.spectra
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.triple-loop-spaces
open import synthetic-homotopy-theory.universal-cover-circle
open import synthetic-homotopy-theory.wedges-of-pointed-types
```

## Tutorials

```agda
open import tutorials.basic-agda
```

## Type theories

```agda
open import type-theories
open import type-theories.comprehension-type-theories
open import type-theories.dependent-type-theories
open import type-theories.fibered-dependent-type-theories
open import type-theories.sections-dependent-type-theories
open import type-theories.simple-type-theories
open import type-theories.unityped-type-theories
```

## Univalent combinatorics

```agda
open import univalent-combinatorics
open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.2-element-subtypes
open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.binomial-types
open import univalent-combinatorics.bracelets
open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.cartesian-products-species
open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.complements-isolated-points
open import univalent-combinatorics.composition-species
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.coproducts-species
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.counting-fibers-of-maps
open import univalent-combinatorics.counting-maybe
open import univalent-combinatorics.counting
open import univalent-combinatorics.cubes
open import univalent-combinatorics.cycle-index-series-species
open import univalent-combinatorics.cycle-partitions
open import univalent-combinatorics.cyclic-types
open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.decidable-equivalence-relations
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dedekind-finite-sets
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.derivatives-species
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.embeddings-standard-finite-types
open import univalent-combinatorics.embeddings
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.equivalences-cubes
open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.equivalences-standard-finite-types
open import univalent-combinatorics.equivalences
open import univalent-combinatorics.exponents-species
open import univalent-combinatorics.ferrers-diagrams
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-connected-components
open import univalent-combinatorics.finite-presentations
open import univalent-combinatorics.finite-species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-presented-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.inequality-types-with-counting
open import univalent-combinatorics.injective-maps
open import univalent-combinatorics.isotopies-latin-squares
open import univalent-combinatorics.kuratowsky-finite-sets
open import univalent-combinatorics.latin-squares
open import univalent-combinatorics.lists
open import univalent-combinatorics.main-classes-of-latin-hypercubes
open import univalent-combinatorics.main-classes-of-latin-squares
open import univalent-combinatorics.maybe
open import univalent-combinatorics.morphisms-finite-species
open import univalent-combinatorics.morphisms-species
open import univalent-combinatorics.necklaces
open import univalent-combinatorics.orientations-complete-undirected-graph
open import univalent-combinatorics.orientations-cubes
open import univalent-combinatorics.partitions
open import univalent-combinatorics.petri-nets
open import univalent-combinatorics.pi-finite-types
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.pointing-species
open import univalent-combinatorics.precategory-of-finite-species
open import univalent-combinatorics.presented-pi-finite-types
open import univalent-combinatorics.quotients-finite-types
open import univalent-combinatorics.ramsey-theory
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.sequences-finite-types
open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.species
open import univalent-combinatorics.standard-finite-pruned-trees
open import univalent-combinatorics.standard-finite-trees
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.steiner-systems
open import univalent-combinatorics.steiner-triple-systems
open import univalent-combinatorics.sums-of-natural-numbers
open import univalent-combinatorics.surjective-maps
open import univalent-combinatorics.symmetric-difference
open import univalent-combinatorics.universal-property-standard-finite-types
open import univalent-combinatorics.unlabeled-partitions
open import univalent-combinatorics.unlabeled-rooted-trees
open import univalent-combinatorics.unlabeled-structures-species
open import univalent-combinatorics.unlabeled-trees
```
