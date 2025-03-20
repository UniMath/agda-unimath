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
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics
  (funext : function-extensionality)
  where

open import univalent-combinatorics.2-element-decidable-subtypes funext public
open import univalent-combinatorics.2-element-subtypes funext public
open import univalent-combinatorics.2-element-types funext public
open import univalent-combinatorics.binomial-types funext public
open import univalent-combinatorics.bracelets funext public
open import univalent-combinatorics.cartesian-product-types funext public
open import univalent-combinatorics.classical-finite-types funext public
open import univalent-combinatorics.complements-isolated-elements funext public
open import univalent-combinatorics.coproduct-types funext public
open import univalent-combinatorics.counting funext public
open import univalent-combinatorics.counting-decidable-subtypes funext public
open import univalent-combinatorics.counting-dependent-pair-types funext public
open import univalent-combinatorics.counting-fibers-of-maps public
open import univalent-combinatorics.counting-maybe funext public
open import univalent-combinatorics.cubes funext public
open import univalent-combinatorics.cycle-partitions funext public
open import univalent-combinatorics.cycle-prime-decomposition-natural-numbers funext public
open import univalent-combinatorics.cyclic-finite-types funext public
open import univalent-combinatorics.de-morgans-law funext public
open import univalent-combinatorics.decidable-dependent-function-types funext public
open import univalent-combinatorics.decidable-dependent-pair-types funext public
open import univalent-combinatorics.decidable-equivalence-relations funext public
open import univalent-combinatorics.decidable-propositions funext public
open import univalent-combinatorics.decidable-subtypes funext public
open import univalent-combinatorics.dedekind-finite-sets funext public
open import univalent-combinatorics.dependent-function-types funext public
open import univalent-combinatorics.dependent-pair-types funext public
open import univalent-combinatorics.discrete-sigma-decompositions funext public
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products funext public
open import univalent-combinatorics.double-counting funext public
open import univalent-combinatorics.embeddings funext public
open import univalent-combinatorics.embeddings-standard-finite-types funext public
open import univalent-combinatorics.equality-finite-types funext public
open import univalent-combinatorics.equality-standard-finite-types funext public
open import univalent-combinatorics.equivalences funext public
open import univalent-combinatorics.equivalences-cubes funext public
open import univalent-combinatorics.equivalences-standard-finite-types funext public
open import univalent-combinatorics.ferrers-diagrams funext public
open import univalent-combinatorics.fibers-of-maps funext public
open import univalent-combinatorics.finite-choice funext public
open import univalent-combinatorics.finite-presentations public
open import univalent-combinatorics.finite-types funext public
open import univalent-combinatorics.finitely-many-connected-components funext public
open import univalent-combinatorics.finitely-presented-types funext public
open import univalent-combinatorics.function-types funext public
open import univalent-combinatorics.image-of-maps funext public
open import univalent-combinatorics.inequality-types-with-counting funext public
open import univalent-combinatorics.inhabited-finite-types funext public
open import univalent-combinatorics.injective-maps funext public
open import univalent-combinatorics.involution-standard-finite-types funext public
open import univalent-combinatorics.isotopies-latin-squares funext public
open import univalent-combinatorics.kuratowski-finite-sets funext public
open import univalent-combinatorics.latin-squares funext public
open import univalent-combinatorics.locally-finite-types funext public
open import univalent-combinatorics.main-classes-of-latin-hypercubes funext public
open import univalent-combinatorics.main-classes-of-latin-squares funext public
open import univalent-combinatorics.maybe funext public
open import univalent-combinatorics.necklaces funext public
open import univalent-combinatorics.orientations-complete-undirected-graph funext public
open import univalent-combinatorics.orientations-cubes funext public
open import univalent-combinatorics.partitions funext public
open import univalent-combinatorics.petri-nets funext public
open import univalent-combinatorics.pi-finite-types funext public
open import univalent-combinatorics.pigeonhole-principle funext public
open import univalent-combinatorics.presented-pi-finite-types public
open import univalent-combinatorics.quotients-finite-types funext public
open import univalent-combinatorics.ramsey-theory funext public
open import univalent-combinatorics.repetitions-of-values funext public
open import univalent-combinatorics.repetitions-of-values-sequences public
open import univalent-combinatorics.retracts-of-finite-types funext public
open import univalent-combinatorics.riffle-shuffles funext public
open import univalent-combinatorics.sequences-finite-types funext public
open import univalent-combinatorics.set-quotients-of-index-two funext public
open import univalent-combinatorics.sigma-decompositions funext public
open import univalent-combinatorics.skipping-element-standard-finite-types funext public
open import univalent-combinatorics.small-types funext public
open import univalent-combinatorics.standard-finite-pruned-trees funext public
open import univalent-combinatorics.standard-finite-trees funext public
open import univalent-combinatorics.standard-finite-types funext public
open import univalent-combinatorics.steiner-systems funext public
open import univalent-combinatorics.steiner-triple-systems funext public
open import univalent-combinatorics.sums-of-natural-numbers funext public
open import univalent-combinatorics.surjective-maps funext public
open import univalent-combinatorics.symmetric-difference funext public
open import univalent-combinatorics.trivial-sigma-decompositions funext public
open import univalent-combinatorics.type-duality funext public
open import univalent-combinatorics.unbounded-pi-finite-types funext public
open import univalent-combinatorics.unions-subtypes funext public
open import univalent-combinatorics.universal-property-standard-finite-types funext public
open import univalent-combinatorics.unlabeled-partitions public
open import univalent-combinatorics.unlabeled-rooted-trees public
open import univalent-combinatorics.unlabeled-trees public
open import univalent-combinatorics.untruncated-pi-finite-types funext public
```

## References

{{#bibliography}}
