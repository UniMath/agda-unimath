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
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import univalent-combinatorics.2-element-decidable-subtypes funext univalence truncations public
open import univalent-combinatorics.2-element-subtypes funext univalence truncations public
open import univalent-combinatorics.2-element-types funext univalence truncations public
open import univalent-combinatorics.binomial-types funext univalence truncations public
open import univalent-combinatorics.bracelets funext univalence truncations public
open import univalent-combinatorics.cartesian-product-types funext univalence truncations public
open import univalent-combinatorics.classical-finite-types funext univalence truncations public
open import univalent-combinatorics.complements-isolated-elements funext univalence truncations public
open import univalent-combinatorics.coproduct-types funext univalence truncations public
open import univalent-combinatorics.counting funext univalence truncations public
open import univalent-combinatorics.counting-decidable-subtypes funext univalence truncations public
open import univalent-combinatorics.counting-dependent-pair-types funext univalence truncations public
open import univalent-combinatorics.counting-fibers-of-maps public
open import univalent-combinatorics.counting-maybe funext univalence truncations public
open import univalent-combinatorics.cubes funext univalence truncations public
open import univalent-combinatorics.cycle-partitions funext univalence truncations public
open import univalent-combinatorics.cycle-prime-decomposition-natural-numbers funext univalence truncations public
open import univalent-combinatorics.cyclic-finite-types funext univalence truncations public
open import univalent-combinatorics.de-morgans-law funext univalence truncations public
open import univalent-combinatorics.decidable-dependent-function-types funext univalence truncations public
open import univalent-combinatorics.decidable-dependent-pair-types funext univalence truncations public
open import univalent-combinatorics.decidable-equivalence-relations funext univalence truncations public
open import univalent-combinatorics.decidable-propositions funext univalence truncations public
open import univalent-combinatorics.decidable-subtypes funext univalence truncations public
open import univalent-combinatorics.dedekind-finite-sets funext univalence public
open import univalent-combinatorics.dependent-function-types funext univalence truncations public
open import univalent-combinatorics.dependent-pair-types funext univalence truncations public
open import univalent-combinatorics.discrete-sigma-decompositions funext univalence truncations public
open import univalent-combinatorics.distributivity-of-set-truncation-over-finite-products funext univalence truncations public
open import univalent-combinatorics.double-counting funext univalence truncations public
open import univalent-combinatorics.embeddings funext univalence truncations public
open import univalent-combinatorics.embeddings-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.equality-finite-types funext univalence truncations public
open import univalent-combinatorics.equality-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.equivalences funext univalence truncations public
open import univalent-combinatorics.equivalences-cubes funext univalence truncations public
open import univalent-combinatorics.equivalences-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.ferrers-diagrams funext univalence truncations public
open import univalent-combinatorics.fibers-of-maps funext univalence truncations public
open import univalent-combinatorics.finite-choice funext univalence truncations public
open import univalent-combinatorics.finite-presentations public
open import univalent-combinatorics.finite-types funext univalence truncations public
open import univalent-combinatorics.finitely-many-connected-components funext univalence truncations public
open import univalent-combinatorics.finitely-presented-types funext univalence truncations public
open import univalent-combinatorics.function-types funext univalence truncations public
open import univalent-combinatorics.image-of-maps funext univalence truncations public
open import univalent-combinatorics.inequality-types-with-counting funext univalence truncations public
open import univalent-combinatorics.inhabited-finite-types funext univalence truncations public
open import univalent-combinatorics.injective-maps funext univalence truncations public
open import univalent-combinatorics.involution-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.isotopies-latin-squares funext univalence truncations public
open import univalent-combinatorics.kuratowski-finite-sets funext univalence truncations public
open import univalent-combinatorics.latin-squares funext univalence truncations public
open import univalent-combinatorics.locally-finite-types funext univalence truncations public
open import univalent-combinatorics.main-classes-of-latin-hypercubes funext univalence truncations public
open import univalent-combinatorics.main-classes-of-latin-squares funext univalence truncations public
open import univalent-combinatorics.maybe funext univalence truncations public
open import univalent-combinatorics.necklaces funext univalence truncations public
open import univalent-combinatorics.orientations-complete-undirected-graph funext univalence truncations public
open import univalent-combinatorics.orientations-cubes funext univalence truncations public
open import univalent-combinatorics.partitions funext univalence truncations public
open import univalent-combinatorics.petri-nets funext univalence truncations public
open import univalent-combinatorics.pi-finite-types funext univalence truncations public
open import univalent-combinatorics.pigeonhole-principle funext univalence truncations public
open import univalent-combinatorics.presented-pi-finite-types public
open import univalent-combinatorics.quotients-finite-types funext univalence truncations public
open import univalent-combinatorics.ramsey-theory funext univalence truncations public
open import univalent-combinatorics.repetitions-of-values funext univalence truncations public
open import univalent-combinatorics.repetitions-of-values-sequences public
open import univalent-combinatorics.retracts-of-finite-types funext univalence truncations public
open import univalent-combinatorics.riffle-shuffles funext univalence truncations public
open import univalent-combinatorics.sequences-finite-types funext univalence truncations public
open import univalent-combinatorics.set-quotients-of-index-two funext univalence truncations public
open import univalent-combinatorics.sigma-decompositions funext univalence truncations public
open import univalent-combinatorics.skipping-element-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.small-types funext univalence truncations public
open import univalent-combinatorics.standard-finite-pruned-trees funext univalence truncations public
open import univalent-combinatorics.standard-finite-trees funext univalence truncations public
open import univalent-combinatorics.standard-finite-types funext univalence truncations public
open import univalent-combinatorics.steiner-systems funext univalence truncations public
open import univalent-combinatorics.steiner-triple-systems funext univalence truncations public
open import univalent-combinatorics.sums-of-natural-numbers funext univalence truncations public
open import univalent-combinatorics.surjective-maps funext univalence truncations public
open import univalent-combinatorics.symmetric-difference funext univalence truncations public
open import univalent-combinatorics.trivial-sigma-decompositions funext univalence truncations public
open import univalent-combinatorics.type-duality funext univalence truncations public
open import univalent-combinatorics.unbounded-pi-finite-types funext univalence truncations public
open import univalent-combinatorics.unions-subtypes funext univalence truncations public
open import univalent-combinatorics.universal-property-standard-finite-types funext univalence truncations public
open import univalent-combinatorics.unlabeled-partitions public
open import univalent-combinatorics.unlabeled-rooted-trees public
open import univalent-combinatorics.unlabeled-trees public
open import univalent-combinatorics.untruncated-pi-finite-types funext univalence truncations public
```

## References

{{#bibliography}}
