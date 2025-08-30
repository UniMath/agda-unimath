# Univalent combinatorics

```agda
{-# OPTIONS --guardedness #-}
```

## Idea

Univalent combinatorics is the study of finite univalent mathematics. Finiteness
in univalent mathematics is expressed by a mere equivalence to a standard finite
object.

Many finite structures naturally organize themselves into groupoids, in which
the isomorphic objects are identified by the univalence axiom. Univalence can
therefore help with counting finite structures up to isomorphism. The main piece
of machinery that helps in this task is the general notion of π-finiteness. A
level `k` π-finite type is a type that has finitely many connected components,
such that all its homotopy groups up to level `k` are finite and all its
homotopy groups above level `k` are trivial. The π-finite types enjoy useful
closure properties, such as closedness under Σ, cartesian products, coproducts,
and closedness under Π under a mild condition {{#cite Anel24}}.

## Modules in the univalent combinatorics namespace

```agda
module univalent-combinatorics where

open import univalent-combinatorics.2-element-decidable-subtypes public
open import univalent-combinatorics.2-element-subtypes public
open import univalent-combinatorics.2-element-types public
open import univalent-combinatorics.binomial-types public
open import univalent-combinatorics.bracelets public
open import univalent-combinatorics.cartesian-product-types public
open import univalent-combinatorics.classical-finite-types public
open import univalent-combinatorics.complements-isolated-elements public
open import univalent-combinatorics.coproduct-types public
open import univalent-combinatorics.coproducts-inhabited-finite-types public
open import univalent-combinatorics.counting public
open import univalent-combinatorics.counting-decidable-subtypes public
open import univalent-combinatorics.counting-dependent-pair-types public
open import univalent-combinatorics.counting-maybe public
open import univalent-combinatorics.cubes public
open import univalent-combinatorics.cycle-partitions public
open import univalent-combinatorics.cycle-prime-decomposition-natural-numbers public
open import univalent-combinatorics.cyclic-finite-types public
open import univalent-combinatorics.de-morgans-law public
open import univalent-combinatorics.decidable-dependent-function-types public
open import univalent-combinatorics.decidable-dependent-pair-types public
open import univalent-combinatorics.decidable-equivalence-relations public
open import univalent-combinatorics.decidable-propositions public
open import univalent-combinatorics.decidable-subtypes public
open import univalent-combinatorics.dedekind-finite-sets public
open import univalent-combinatorics.dedekind-finite-types public
open import univalent-combinatorics.dependent-function-types public
open import univalent-combinatorics.dependent-pair-types public
open import univalent-combinatorics.discrete-sigma-decompositions public
open import univalent-combinatorics.disjunction public
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products public
open import univalent-combinatorics.double-counting public
open import univalent-combinatorics.dual-dedekind-finite-types public
open import univalent-combinatorics.embeddings public
open import univalent-combinatorics.embeddings-standard-finite-types public
open import univalent-combinatorics.equality-finite-types public
open import univalent-combinatorics.equality-standard-finite-types public
open import univalent-combinatorics.equivalences public
open import univalent-combinatorics.equivalences-cubes public
open import univalent-combinatorics.equivalences-standard-finite-types public
open import univalent-combinatorics.ferrers-diagrams public
open import univalent-combinatorics.fibers-of-maps public
open import univalent-combinatorics.finite-choice public
open import univalent-combinatorics.finite-subtypes public
open import univalent-combinatorics.finite-types public
open import univalent-combinatorics.finitely-enumerable-subtypes public
open import univalent-combinatorics.finitely-enumerable-types public
open import univalent-combinatorics.finitely-many-connected-components public
open import univalent-combinatorics.finitely-presented-types public
open import univalent-combinatorics.function-types public
open import univalent-combinatorics.image-of-maps public
open import univalent-combinatorics.inequality-types-with-counting public
open import univalent-combinatorics.inhabited-finite-types public
open import univalent-combinatorics.injective-maps public
open import univalent-combinatorics.involution-standard-finite-types public
open import univalent-combinatorics.isotopies-latin-squares public
open import univalent-combinatorics.kuratowski-finite-sets public
open import univalent-combinatorics.latin-squares public
open import univalent-combinatorics.locally-finite-types public
open import univalent-combinatorics.main-classes-of-latin-hypercubes public
open import univalent-combinatorics.main-classes-of-latin-squares public
open import univalent-combinatorics.maybe public
open import univalent-combinatorics.necklaces public
open import univalent-combinatorics.orientations-complete-undirected-graph public
open import univalent-combinatorics.orientations-cubes public
open import univalent-combinatorics.partitions public
open import univalent-combinatorics.petri-nets public
open import univalent-combinatorics.pi-finite-types public
open import univalent-combinatorics.pigeonhole-principle public
open import univalent-combinatorics.presented-pi-finite-types public
open import univalent-combinatorics.quotients-finite-types public
open import univalent-combinatorics.ramsey-theory public
open import univalent-combinatorics.repetitions-of-values public
open import univalent-combinatorics.repetitions-of-values-sequences public
open import univalent-combinatorics.retracts-of-finite-types public
open import univalent-combinatorics.riffle-shuffles public
open import univalent-combinatorics.sequences-finite-types public
open import univalent-combinatorics.set-quotients-of-index-two public
open import univalent-combinatorics.sigma-decompositions public
open import univalent-combinatorics.skipping-element-standard-finite-types public
open import univalent-combinatorics.small-types public
open import univalent-combinatorics.standard-finite-pruned-trees public
open import univalent-combinatorics.standard-finite-trees public
open import univalent-combinatorics.standard-finite-types public
open import univalent-combinatorics.steiner-systems public
open import univalent-combinatorics.steiner-triple-systems public
open import univalent-combinatorics.subcounting public
open import univalent-combinatorics.subfinite-indexing public
open import univalent-combinatorics.subfinite-types public
open import univalent-combinatorics.subfinitely-enumerable-types public
open import univalent-combinatorics.sums-of-natural-numbers public
open import univalent-combinatorics.surjective-maps public
open import univalent-combinatorics.symmetric-difference public
open import univalent-combinatorics.trivial-sigma-decompositions public
open import univalent-combinatorics.truncated-pi-finite-types public
open import univalent-combinatorics.type-duality public
open import univalent-combinatorics.unbounded-pi-finite-types public
open import univalent-combinatorics.unions-subtypes public
open import univalent-combinatorics.universal-property-standard-finite-types public
open import univalent-combinatorics.unlabeled-partitions public
open import univalent-combinatorics.unlabeled-rooted-trees public
open import univalent-combinatorics.unlabeled-trees public
open import univalent-combinatorics.untruncated-pi-finite-types public
```

## References

{{#bibliography}}
