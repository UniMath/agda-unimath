# Foundation

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the foundation namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation.0-connected-types funext univalence truncations public
open import foundation.0-images-of-maps funext univalence truncations public
open import foundation.0-maps funext public
open import foundation.1-types funext univalence public
open import foundation.2-types public
open import foundation.action-on-equivalences-functions funext univalence public
open import foundation.action-on-equivalences-functions-out-of-subuniverses funext univalence public
open import foundation.action-on-equivalences-type-families funext univalence public
open import foundation.action-on-equivalences-type-families-over-subuniverses funext univalence public
open import foundation.action-on-higher-identifications-functions funext public
open import foundation.action-on-homotopies-functions funext public
open import foundation.action-on-identifications-binary-dependent-functions public
open import foundation.action-on-identifications-binary-functions public
open import foundation.action-on-identifications-dependent-functions public
open import foundation.action-on-identifications-functions public
open import foundation.apartness-relations funext univalence truncations public
open import foundation.arithmetic-law-coproduct-and-sigma-decompositions funext univalence truncations public
open import foundation.arithmetic-law-product-and-pi-decompositions funext univalence truncations public
open import foundation.automorphisms funext univalence public
open import foundation.axiom-of-choice funext univalence truncations public
open import foundation.bands funext univalence truncations public
open import foundation.base-changes-span-diagrams funext univalence truncations public
open import foundation.bicomposition-functions funext public
open import foundation.binary-dependent-identifications public
open import foundation.binary-embeddings funext public
open import foundation.binary-equivalences public
open import foundation.binary-equivalences-unordered-pairs-of-types funext univalence truncations public
open import foundation.binary-functoriality-set-quotients funext univalence truncations public
open import foundation.binary-homotopies funext public
open import foundation.binary-operations-unordered-pairs-of-types funext univalence truncations public
open import foundation.binary-reflecting-maps-equivalence-relations funext univalence truncations public
open import foundation.binary-relations funext univalence truncations public
open import foundation.binary-relations-with-extensions funext univalence truncations public
open import foundation.binary-relations-with-lifts funext univalence truncations public
open import foundation.binary-transport public
open import foundation.binary-type-duality funext univalence public
open import foundation.booleans funext univalence truncations public
open import foundation.cantor-schroder-bernstein-escardo funext univalence truncations public
open import foundation.cantors-theorem funext univalence truncations public
open import foundation.cartesian-morphisms-arrows funext univalence truncations public
open import foundation.cartesian-morphisms-span-diagrams funext univalence truncations public
open import foundation.cartesian-product-types funext univalence public
open import foundation.cartesian-products-set-quotients funext univalence truncations public
open import foundation.category-of-families-of-sets funext univalence truncations public
open import foundation.category-of-sets funext univalence truncations public
open import foundation.choice-of-representatives-equivalence-relation funext univalence truncations public
open import foundation.coalgebras-maybe funext univalence public
open import foundation.codiagonal-maps-of-types public
open import foundation.coherently-idempotent-maps funext univalence truncations public
open import foundation.coherently-invertible-maps funext public
open import foundation.coinhabited-pairs-of-types funext univalence truncations public
open import foundation.commuting-cubes-of-maps funext univalence public
open import foundation.commuting-hexagons-of-identifications public
open import foundation.commuting-pentagons-of-identifications public
open import foundation.commuting-prisms-of-maps funext univalence public
open import foundation.commuting-squares-of-homotopies funext public
open import foundation.commuting-squares-of-identifications funext public
open import foundation.commuting-squares-of-maps funext univalence public
open import foundation.commuting-tetrahedra-of-homotopies funext public
open import foundation.commuting-tetrahedra-of-maps public
open import foundation.commuting-triangles-of-homotopies funext public
open import foundation.commuting-triangles-of-identifications funext public
open import foundation.commuting-triangles-of-maps funext univalence public
open import foundation.commuting-triangles-of-morphisms-arrows funext public
open import foundation.complements public
open import foundation.complements-subtypes funext univalence truncations public
open import foundation.composite-maps-in-inverse-sequential-diagrams funext univalence truncations public
open import foundation.composition-algebra funext public
open import foundation.composition-spans funext univalence truncations public
open import foundation.computational-identity-types funext univalence public
open import foundation.cones-over-cospan-diagrams funext public
open import foundation.cones-over-inverse-sequential-diagrams funext univalence truncations public
open import foundation.conjunction funext univalence truncations public
open import foundation.connected-components funext univalence truncations public
open import foundation.connected-components-universes funext univalence truncations public
open import foundation.connected-maps funext univalence truncations public
open import foundation.connected-types funext univalence truncations public
open import foundation.constant-maps funext univalence truncations public
open import foundation.constant-span-diagrams funext univalence public
open import foundation.constant-type-families funext public
open import foundation.continuations funext univalence truncations public
open import foundation.contractible-maps funext public
open import foundation.contractible-types funext univalence public
open import foundation.copartial-elements funext univalence truncations public
open import foundation.copartial-functions funext univalence truncations public
open import foundation.coproduct-decompositions funext univalence truncations public
open import foundation.coproduct-decompositions-subuniverse funext univalence truncations public
open import foundation.coproduct-types funext univalence truncations public
open import foundation.coproducts-pullbacks funext univalence truncations public
open import foundation.coslice funext public
open import foundation.cospan-diagrams public
open import foundation.cospans public
open import foundation.decidable-dependent-function-types funext univalence truncations public
open import foundation.decidable-dependent-pair-types funext univalence truncations public
open import foundation.decidable-embeddings funext univalence truncations public
open import foundation.decidable-equality funext univalence truncations public
open import foundation.decidable-equivalence-relations funext univalence truncations public
open import foundation.decidable-maps funext univalence truncations public
open import foundation.decidable-propositions funext univalence truncations public
open import foundation.decidable-relations funext univalence truncations public
open import foundation.decidable-subtypes funext univalence truncations public
open import foundation.decidable-types funext univalence truncations public
open import foundation.dependent-binary-homotopies funext public
open import foundation.dependent-binomial-theorem funext univalence truncations public
open import foundation.dependent-epimorphisms funext univalence truncations public
open import foundation.dependent-epimorphisms-with-respect-to-truncated-types funext univalence truncations public
open import foundation.dependent-function-types funext univalence public
open import foundation.dependent-homotopies public
open import foundation.dependent-identifications funext public
open import foundation.dependent-inverse-sequential-diagrams funext univalence truncations public
open import foundation.dependent-pair-types public
open import foundation.dependent-products-contractible-types funext public
open import foundation.dependent-products-propositions funext public
open import foundation.dependent-products-pullbacks funext univalence public
open import foundation.dependent-products-truncated-types funext public
open import foundation.dependent-sequences public
open import foundation.dependent-sums-pullbacks funext public
open import foundation.dependent-telescopes public
open import foundation.dependent-universal-property-equivalences funext public
open import foundation.descent-coproduct-types funext univalence truncations public
open import foundation.descent-dependent-pair-types funext public
open import foundation.descent-empty-types funext public
open import foundation.descent-equivalences funext public
open import foundation.diaconescus-theorem funext univalence truncations public
open import foundation.diagonal-maps-cartesian-products-of-types funext univalence public
open import foundation.diagonal-maps-of-types funext public
open import foundation.diagonal-span-diagrams funext public
open import foundation.diagonals-of-maps funext public
open import foundation.diagonals-of-morphisms-arrows public
open import foundation.discrete-binary-relations funext univalence truncations public
open import foundation.discrete-reflexive-relations funext univalence truncations public
open import foundation.discrete-relaxed-sigma-decompositions funext univalence public
open import foundation.discrete-sigma-decompositions funext univalence truncations public
open import foundation.discrete-types funext univalence truncations public
open import foundation.disjoint-subtypes funext univalence truncations public
open import foundation.disjunction funext univalence truncations public
open import foundation.double-arrows public
open import foundation.double-negation funext univalence truncations public
open import foundation.double-negation-modality funext univalence truncations public
open import foundation.double-negation-stable-equality funext univalence truncations public
open import foundation.double-negation-stable-propositions funext univalence truncations public
open import foundation.double-powersets funext univalence truncations public
open import foundation.dubuc-penon-compact-types funext univalence truncations public
open import foundation.effective-maps-equivalence-relations funext univalence truncations public
open import foundation.embeddings funext public
open import foundation.empty-types funext univalence truncations public
open import foundation.endomorphisms funext univalence truncations public
open import foundation.epimorphisms funext univalence truncations public
open import foundation.epimorphisms-with-respect-to-sets funext univalence truncations public
open import foundation.epimorphisms-with-respect-to-truncated-types funext univalence truncations public
open import foundation.equality-cartesian-product-types public
open import foundation.equality-coproduct-types funext univalence truncations public
open import foundation.equality-dependent-function-types funext public
open import foundation.equality-dependent-pair-types funext public
open import foundation.equality-fibers-of-maps funext public
open import foundation.equivalence-classes funext univalence truncations public
open import foundation.equivalence-extensionality funext public
open import foundation.equivalence-induction funext univalence public
open import foundation.equivalence-injective-type-families funext univalence public
open import foundation.equivalence-relations funext univalence truncations public
open import foundation.equivalences funext public
open import foundation.equivalences-arrows funext univalence truncations public
open import foundation.equivalences-cospans funext univalence public
open import foundation.equivalences-double-arrows funext univalence truncations public
open import foundation.equivalences-inverse-sequential-diagrams funext univalence truncations public
open import foundation.equivalences-maybe funext univalence truncations public
open import foundation.equivalences-span-diagrams funext univalence truncations public
open import foundation.equivalences-span-diagrams-families-of-types funext univalence public
open import foundation.equivalences-spans funext univalence public
open import foundation.equivalences-spans-families-of-types funext univalence public
open import foundation.evaluation-functions public
open import foundation.exclusive-disjunction funext univalence truncations public
open import foundation.exclusive-sum funext univalence truncations public
open import foundation.existential-quantification funext univalence truncations public
open import foundation.exponents-set-quotients funext univalence truncations public
open import foundation.extensions-types funext univalence truncations public
open import foundation.extensions-types-global-subuniverses funext univalence truncations public
open import foundation.extensions-types-subuniverses funext univalence truncations public
open import foundation.faithful-maps funext public
open import foundation.families-of-equivalences funext public
open import foundation.families-of-maps funext public
open import foundation.families-over-telescopes public
open import foundation.fiber-inclusions funext univalence public
open import foundation.fibered-equivalences funext univalence truncations public
open import foundation.fibered-involutions funext univalence truncations public
open import foundation.fibered-maps funext univalence truncations public
open import foundation.fibers-of-maps funext public
open import foundation.finitely-coherent-equivalences funext public
open import foundation.finitely-coherently-invertible-maps funext public
open import foundation.fixed-points-endofunctions public
open import foundation.full-subtypes funext univalence truncations public
open import foundation.function-extensionality funext public
open import foundation.function-extensionality-axiom public
open import foundation.function-types funext public
open import foundation.functional-correspondences funext univalence truncations public
open import foundation.functoriality-action-on-identifications-functions funext public
open import foundation.functoriality-cartesian-product-types funext public
open import foundation.functoriality-coproduct-types funext univalence truncations public
open import foundation.functoriality-dependent-function-types funext univalence public
open import foundation.functoriality-dependent-pair-types funext public
open import foundation.functoriality-fibers-of-maps funext public
open import foundation.functoriality-function-types funext univalence public
open import foundation.functoriality-morphisms-arrows funext univalence truncations public
open import foundation.functoriality-propositional-truncation funext univalence truncations public
open import foundation.functoriality-pullbacks funext univalence truncations public
open import foundation.functoriality-sequential-limits funext univalence truncations public
open import foundation.functoriality-set-quotients funext univalence truncations public
open import foundation.functoriality-set-truncation funext univalence truncations public
open import foundation.functoriality-truncation funext univalence truncations public
open import foundation.fundamental-theorem-of-equivalence-relations funext univalence truncations public
open import foundation.fundamental-theorem-of-identity-types public
open import foundation.global-choice funext univalence truncations public
open import foundation.global-subuniverses funext univalence public
open import foundation.globular-type-of-dependent-functions funext univalence truncations public
open import foundation.globular-type-of-functions funext univalence truncations public
open import foundation.higher-homotopies-morphisms-arrows funext univalence truncations public
open import foundation.hilberts-epsilon-operators funext univalence truncations public
open import foundation.homotopies funext public
open import foundation.homotopies-morphisms-arrows funext public
open import foundation.homotopies-morphisms-cospan-diagrams funext univalence truncations public
open import foundation.homotopy-algebra public
open import foundation.homotopy-induction funext public
open import foundation.homotopy-preorder-of-types funext univalence truncations public
open import foundation.horizontal-composition-spans-of-spans funext univalence truncations public
open import foundation.idempotent-maps funext public
open import foundation.identity-systems public
open import foundation.identity-truncated-types funext univalence public
open import foundation.identity-types funext public
open import foundation.images funext univalence truncations public
open import foundation.images-subtypes funext univalence truncations public
open import foundation.implicit-function-types public
open import foundation.impredicative-encodings funext univalence truncations public
open import foundation.impredicative-universes funext univalence truncations public
open import foundation.induction-principle-propositional-truncation public
open import foundation.infinitely-coherent-equivalences funext univalence public
open import foundation.inhabited-subtypes funext univalence truncations public
open import foundation.inhabited-types funext univalence truncations public
open import foundation.injective-maps funext public
open import foundation.interchange-law public
open import foundation.intersections-subtypes funext univalence truncations public
open import foundation.inverse-sequential-diagrams funext univalence truncations public
open import foundation.invertible-maps funext univalence truncations public
open import foundation.involutions funext univalence public
open import foundation.irrefutable-propositions funext univalence truncations public
open import foundation.isolated-elements funext univalence truncations public
open import foundation.isomorphisms-of-sets funext univalence public
open import foundation.iterated-cartesian-product-types funext univalence truncations public
open import foundation.iterated-dependent-pair-types public
open import foundation.iterated-dependent-product-types funext public
open import foundation.iterating-automorphisms funext univalence truncations public
open import foundation.iterating-families-of-maps funext univalence truncations public
open import foundation.iterating-functions funext univalence truncations public
open import foundation.iterating-involutions funext univalence truncations public
open import foundation.kernel-span-diagrams-of-maps funext public
open import foundation.large-apartness-relations funext univalence truncations public
open import foundation.large-binary-relations funext univalence truncations public
open import foundation.large-dependent-pair-types public
open import foundation.large-homotopies public
open import foundation.large-identity-types public
open import foundation.large-locale-of-propositions funext univalence truncations public
open import foundation.large-locale-of-subtypes funext univalence truncations public
open import foundation.law-of-excluded-middle funext univalence truncations public
open import foundation.lawveres-fixed-point-theorem funext univalence truncations public
open import foundation.lesser-limited-principle-of-omniscience funext univalence truncations public
open import foundation.lifts-types public
open import foundation.limited-principle-of-omniscience funext univalence truncations public
open import foundation.locale-of-propositions funext univalence truncations public
open import foundation.locally-small-types funext univalence truncations public
open import foundation.logical-equivalences funext public
open import foundation.maps-in-global-subuniverses funext univalence truncations public
open import foundation.maps-in-subuniverses funext univalence public
open import foundation.maybe funext univalence truncations public
open import foundation.mere-embeddings funext univalence truncations public
open import foundation.mere-equality funext univalence truncations public
open import foundation.mere-equivalences funext univalence truncations public
open import foundation.mere-functions funext univalence truncations public
open import foundation.mere-logical-equivalences funext univalence truncations public
open import foundation.mere-path-cosplit-maps funext univalence truncations public
open import foundation.monomorphisms funext univalence public
open import foundation.morphisms-arrows funext public
open import foundation.morphisms-binary-relations funext univalence truncations public
open import foundation.morphisms-coalgebras-maybe funext univalence public
open import foundation.morphisms-cospan-diagrams public
open import foundation.morphisms-cospans public
open import foundation.morphisms-double-arrows funext univalence public
open import foundation.morphisms-inverse-sequential-diagrams funext univalence truncations public
open import foundation.morphisms-span-diagrams funext univalence truncations public
open import foundation.morphisms-spans public
open import foundation.morphisms-spans-families-of-types funext public
open import foundation.morphisms-twisted-arrows public
open import foundation.multisubsets funext univalence truncations public
open import foundation.multivariable-correspondences funext univalence truncations public
open import foundation.multivariable-decidable-relations funext univalence truncations public
open import foundation.multivariable-functoriality-set-quotients funext univalence truncations public
open import foundation.multivariable-homotopies funext public
open import foundation.multivariable-operations funext univalence truncations public
open import foundation.multivariable-relations funext univalence truncations public
open import foundation.multivariable-sections funext public
open import foundation.negated-equality funext univalence truncations public
open import foundation.negation funext public
open import foundation.noncontractible-types funext univalence truncations public
open import foundation.null-homotopic-maps funext univalence truncations public
open import foundation.operations-span-diagrams funext univalence truncations public
open import foundation.operations-spans funext univalence truncations public
open import foundation.operations-spans-families-of-types public
open import foundation.opposite-spans public
open import foundation.pairs-of-distinct-elements funext univalence truncations public
open import foundation.partial-elements public
open import foundation.partial-functions public
open import foundation.partial-sequences public
open import foundation.partitions funext univalence truncations public
open import foundation.path-algebra funext public
open import foundation.path-cosplit-maps funext univalence truncations public
open import foundation.path-split-maps funext public
open import foundation.path-split-type-families funext public
open import foundation.perfect-images funext univalence truncations public
open import foundation.permutations-spans-families-of-types public
open import foundation.pi-decompositions funext univalence public
open import foundation.pi-decompositions-subuniverse funext univalence public
open import foundation.pointed-torsorial-type-families funext univalence truncations public
open import foundation.postcomposition-dependent-functions funext public
open import foundation.postcomposition-functions funext public
open import foundation.postcomposition-pullbacks funext public
open import foundation.powersets funext univalence truncations public
open import foundation.precomposition-dependent-functions funext public
open import foundation.precomposition-functions funext public
open import foundation.precomposition-functions-into-subuniverses funext public
open import foundation.precomposition-type-families funext public
open import foundation.preunivalence funext univalence public
open import foundation.preunivalent-type-families funext univalence public
open import foundation.principle-of-omniscience funext univalence truncations public
open import foundation.product-decompositions public
open import foundation.product-decompositions-subuniverse funext univalence public
open import foundation.products-binary-relations funext univalence truncations public
open import foundation.products-equivalence-relations funext univalence truncations public
open import foundation.products-of-tuples-of-types funext univalence truncations public
open import foundation.products-pullbacks funext univalence truncations public
open import foundation.products-unordered-pairs-of-types funext univalence truncations public
open import foundation.products-unordered-tuples-of-types funext univalence truncations public
open import foundation.projective-types funext univalence truncations public
open import foundation.proper-subtypes funext univalence truncations public
open import foundation.propositional-extensionality funext univalence truncations public
open import foundation.propositional-maps funext public
open import foundation.propositional-resizing funext univalence truncations public
open import foundation.propositional-truncations funext univalence public
open import foundation.propositions funext univalence public
open import foundation.pullback-cones funext univalence truncations public
open import foundation.pullbacks funext univalence truncations public
open import foundation.pullbacks-subtypes funext univalence truncations public
open import foundation.quasicoherently-idempotent-maps funext univalence truncations public
open import foundation.raising-universe-levels funext univalence public
open import foundation.raising-universe-levels-booleans public
open import foundation.raising-universe-levels-unit-type public
open import foundation.reflecting-maps-equivalence-relations funext univalence truncations public
open import foundation.reflexive-relations funext univalence truncations public
open import foundation.regensburg-extension-fundamental-theorem-of-identity-types funext univalence truncations public
open import foundation.relaxed-sigma-decompositions funext univalence public
open import foundation.repetitions-of-values funext univalence truncations public
open import foundation.repetitions-sequences funext univalence truncations public
open import foundation.replacement funext univalence truncations public
open import foundation.retractions funext public
open import foundation.retracts-of-maps funext univalence public
open import foundation.retracts-of-types funext univalence public
open import foundation.sections funext public
open import foundation.separated-types-subuniverses funext univalence public
open import foundation.sequences public
open import foundation.sequential-limits funext univalence truncations public
open import foundation.set-presented-types funext univalence truncations public
open import foundation.set-quotients funext univalence truncations public
open import foundation.set-truncations funext univalence public
open import foundation.sets funext univalence public
open import foundation.shifting-sequences public
open import foundation.sigma-closed-subuniverses funext univalence public
open import foundation.sigma-decomposition-subuniverse funext univalence public
open import foundation.sigma-decompositions funext univalence truncations public
open import foundation.singleton-induction public
open import foundation.singleton-subtypes funext univalence truncations public
open import foundation.slice funext univalence public
open import foundation.small-maps funext univalence truncations public
open import foundation.small-types funext univalence truncations public
open import foundation.small-universes funext univalence truncations public
open import foundation.sorial-type-families public
open import foundation.span-diagrams funext public
open import foundation.span-diagrams-families-of-types public
open import foundation.spans public
open import foundation.spans-families-of-types public
open import foundation.spans-of-spans funext univalence public
open import foundation.split-idempotent-maps funext univalence truncations public
open import foundation.split-surjective-maps public
open import foundation.standard-apartness-relations funext univalence truncations public
open import foundation.standard-pullbacks funext public
open import foundation.standard-ternary-pullbacks funext public
open import foundation.strict-symmetrization-binary-relations funext univalence truncations public
open import foundation.strictly-involutive-identity-types funext univalence public
open import foundation.strictly-right-unital-concatenation-identifications public
open import foundation.strong-preunivalence funext univalence truncations public
open import foundation.strongly-extensional-maps funext univalence truncations public
open import foundation.structure funext univalence public
open import foundation.structure-identity-principle public
open import foundation.structured-equality-duality funext univalence public
open import foundation.structured-type-duality funext univalence truncations public
open import foundation.subsingleton-induction public
open import foundation.subterminal-types public
open import foundation.subtype-duality funext univalence truncations public
open import foundation.subtype-identity-principle public
open import foundation.subtypes funext univalence truncations public
open import foundation.subuniverses funext univalence public
open import foundation.surjective-maps funext univalence truncations public
open import foundation.symmetric-binary-relations funext univalence truncations public
open import foundation.symmetric-cores-binary-relations funext univalence truncations public
open import foundation.symmetric-difference funext univalence truncations public
open import foundation.symmetric-identity-types funext univalence truncations public
open import foundation.symmetric-operations funext univalence truncations public
open import foundation.telescopes public
open import foundation.terminal-spans-families-of-types funext public
open import foundation.tight-apartness-relations funext univalence truncations public
open import foundation.torsorial-type-families funext univalence truncations public
open import foundation.total-partial-elements public
open import foundation.total-partial-functions funext public
open import foundation.transfinite-cocomposition-of-maps funext univalence truncations public
open import foundation.transport-along-equivalences funext univalence public
open import foundation.transport-along-higher-identifications funext public
open import foundation.transport-along-homotopies funext public
open import foundation.transport-along-identifications public
open import foundation.transport-split-type-families funext univalence public
open import foundation.transposition-identifications-along-equivalences funext public
open import foundation.transposition-identifications-along-retractions funext public
open import foundation.transposition-identifications-along-sections funext public
open import foundation.transposition-span-diagrams funext public
open import foundation.trivial-relaxed-sigma-decompositions funext univalence public
open import foundation.trivial-sigma-decompositions funext univalence truncations public
open import foundation.truncated-equality funext univalence truncations public
open import foundation.truncated-maps funext public
open import foundation.truncated-types funext univalence public
open import foundation.truncation-equivalences funext univalence truncations public
open import foundation.truncation-images-of-maps funext univalence truncations public
open import foundation.truncation-levels public
open import foundation.truncation-modalities funext univalence truncations public
open import foundation.truncations funext univalence truncations public
open import foundation.tuples-of-types funext univalence truncations public
open import foundation.type-arithmetic-booleans public
open import foundation.type-arithmetic-cartesian-product-types public
open import foundation.type-arithmetic-coproduct-types funext univalence truncations public
open import foundation.type-arithmetic-dependent-function-types funext univalence public
open import foundation.type-arithmetic-dependent-pair-types public
open import foundation.type-arithmetic-empty-type funext univalence truncations public
open import foundation.type-arithmetic-standard-pullbacks funext public
open import foundation.type-arithmetic-unit-type funext public
open import foundation.type-duality funext univalence truncations public
open import foundation.type-theoretic-principle-of-choice funext public
open import foundation.uniformly-decidable-type-families funext univalence truncations public
open import foundation.unions-subtypes funext univalence truncations public
open import foundation.uniqueness-image funext univalence truncations public
open import foundation.uniqueness-quantification funext univalence truncations public
open import foundation.uniqueness-set-quotients funext univalence truncations public
open import foundation.uniqueness-set-truncations funext univalence public
open import foundation.uniqueness-truncation funext public
open import foundation.unit-type public
open import foundation.unital-binary-operations public
open import foundation.univalence funext univalence public
open import foundation.univalence-implies-function-extensionality funext univalence truncations public
open import foundation.univalent-type-families funext univalence public
open import foundation.universal-property-booleans funext public
open import foundation.universal-property-cartesian-product-types funext public
open import foundation.universal-property-contractible-types funext public
open import foundation.universal-property-coproduct-types funext public
open import foundation.universal-property-dependent-function-types funext public
open import foundation.universal-property-dependent-pair-types funext public
open import foundation.universal-property-empty-type funext public
open import foundation.universal-property-equivalences funext public
open import foundation.universal-property-family-of-fibers-of-maps funext public
open import foundation.universal-property-fiber-products funext public
open import foundation.universal-property-identity-systems funext public
open import foundation.universal-property-identity-types funext univalence truncations public
open import foundation.universal-property-image funext univalence truncations public
open import foundation.universal-property-maybe funext public
open import foundation.universal-property-propositional-truncation funext public
open import foundation.universal-property-propositional-truncation-into-sets funext univalence truncations public
open import foundation.universal-property-pullbacks funext public
open import foundation.universal-property-sequential-limits funext univalence truncations public
open import foundation.universal-property-set-quotients funext univalence truncations public
open import foundation.universal-property-set-truncation funext univalence truncations public
open import foundation.universal-property-truncation funext univalence truncations public
open import foundation.universal-property-unit-type funext public
open import foundation.universal-quantification funext univalence truncations public
open import foundation.universe-levels public
open import foundation.unordered-pairs funext univalence truncations public
open import foundation.unordered-pairs-of-types funext univalence truncations public
open import foundation.unordered-tuples funext univalence truncations public
open import foundation.unordered-tuples-of-types funext univalence truncations public
open import foundation.vectors-set-quotients funext univalence truncations public
open import foundation.vertical-composition-spans-of-spans funext univalence truncations public
open import foundation.weak-function-extensionality funext univalence truncations public
open import foundation.weak-limited-principle-of-omniscience funext univalence truncations public
open import foundation.weakly-constant-maps funext public
open import foundation.whiskering-higher-homotopies-composition public
open import foundation.whiskering-homotopies-composition public
open import foundation.whiskering-homotopies-concatenation funext public
open import foundation.whiskering-identifications-concatenation funext public
open import foundation.whiskering-operations public
open import foundation.wild-category-of-types funext univalence truncations public
open import foundation.yoneda-identity-types funext univalence public
```
