# Category theory

## Examples of categories and large categories

{{#include tables/categories.md}}

## Examples of precategories and large precategories

{{#include tables/precategories.md}}

## Modules in the category theory namespace

```agda
open import foundation.function-extensionality-axiom

module
  category-theory
  (funext : function-extensionality)
  where

open import category-theory.adjunctions-large-categories funext public
open import category-theory.adjunctions-large-precategories funext public
open import category-theory.anafunctors-categories funext public
open import category-theory.anafunctors-precategories funext public
open import category-theory.augmented-simplex-category funext public
open import category-theory.categories funext public
open import category-theory.category-of-functors funext public
open import category-theory.category-of-functors-from-small-to-large-categories funext public
open import category-theory.category-of-maps-categories funext public
open import category-theory.category-of-maps-from-small-to-large-categories funext public
open import category-theory.commuting-squares-of-morphisms-in-large-precategories funext public
open import category-theory.commuting-squares-of-morphisms-in-precategories funext public
open import category-theory.commuting-squares-of-morphisms-in-set-magmoids funext public
open import category-theory.commuting-triangles-of-morphisms-in-precategories funext public
open import category-theory.commuting-triangles-of-morphisms-in-set-magmoids funext public
open import category-theory.complete-precategories funext public
open import category-theory.composition-operations-on-binary-families-of-sets funext public
open import category-theory.cones-precategories funext public
open import category-theory.conservative-functors-precategories funext public
open import category-theory.constant-functors funext public
open import category-theory.copresheaf-categories funext public
open import category-theory.coproducts-in-precategories funext public
open import category-theory.cores-categories funext public
open import category-theory.cores-precategories funext public
open import category-theory.coslice-precategories funext public
open import category-theory.dependent-composition-operations-over-precategories funext public
open import category-theory.dependent-products-of-categories funext public
open import category-theory.dependent-products-of-large-categories funext public
open import category-theory.dependent-products-of-large-precategories funext public
open import category-theory.dependent-products-of-precategories funext public
open import category-theory.discrete-categories funext public
open import category-theory.displayed-precategories funext public
open import category-theory.embedding-maps-precategories funext public
open import category-theory.embeddings-precategories funext public
open import category-theory.endomorphisms-in-categories funext public
open import category-theory.endomorphisms-in-precategories funext public
open import category-theory.epimorphisms-in-large-precategories funext public
open import category-theory.equivalences-of-categories funext public
open import category-theory.equivalences-of-large-precategories funext public
open import category-theory.equivalences-of-precategories funext public
open import category-theory.essential-fibers-of-functors-precategories funext public
open import category-theory.essentially-injective-functors-precategories funext public
open import category-theory.essentially-surjective-functors-precategories funext public
open import category-theory.exponential-objects-precategories funext public
open import category-theory.extensions-of-functors-precategories funext public
open import category-theory.faithful-functors-precategories funext public
open import category-theory.faithful-maps-precategories funext public
open import category-theory.full-functors-precategories funext public
open import category-theory.full-large-subcategories funext public
open import category-theory.full-large-subprecategories funext public
open import category-theory.full-maps-precategories funext public
open import category-theory.full-subcategories funext public
open import category-theory.full-subprecategories funext public
open import category-theory.fully-faithful-functors-precategories funext public
open import category-theory.fully-faithful-maps-precategories funext public
open import category-theory.function-categories funext public
open import category-theory.function-precategories funext public
open import category-theory.functors-categories funext public
open import category-theory.functors-from-small-to-large-categories funext public
open import category-theory.functors-from-small-to-large-precategories funext public
open import category-theory.functors-large-categories funext public
open import category-theory.functors-large-precategories funext public
open import category-theory.functors-nonunital-precategories funext public
open import category-theory.functors-precategories funext public
open import category-theory.functors-set-magmoids funext public
open import category-theory.gaunt-categories funext public
open import category-theory.groupoids funext public
open import category-theory.homotopies-natural-transformations-large-precategories funext public
open import category-theory.indiscrete-precategories funext public
open import category-theory.initial-category funext public
open import category-theory.initial-objects-large-categories funext public
open import category-theory.initial-objects-large-precategories funext public
open import category-theory.initial-objects-precategories funext public
open import category-theory.isomorphism-induction-categories funext public
open import category-theory.isomorphism-induction-precategories funext public
open import category-theory.isomorphisms-in-categories funext public
open import category-theory.isomorphisms-in-large-categories funext public
open import category-theory.isomorphisms-in-large-precategories funext public
open import category-theory.isomorphisms-in-precategories funext public
open import category-theory.isomorphisms-in-subprecategories funext public
open import category-theory.large-categories funext public
open import category-theory.large-function-categories funext public
open import category-theory.large-function-precategories funext public
open import category-theory.large-precategories funext public
open import category-theory.large-subcategories funext public
open import category-theory.large-subprecategories funext public
open import category-theory.limits-precategories funext public
open import category-theory.maps-categories funext public
open import category-theory.maps-from-small-to-large-categories funext public
open import category-theory.maps-from-small-to-large-precategories funext public
open import category-theory.maps-precategories funext public
open import category-theory.maps-set-magmoids funext public
open import category-theory.monads-on-categories funext public
open import category-theory.monads-on-precategories funext public
open import category-theory.monomorphisms-in-large-precategories funext public
open import category-theory.natural-isomorphisms-functors-categories funext public
open import category-theory.natural-isomorphisms-functors-large-precategories funext public
open import category-theory.natural-isomorphisms-functors-precategories funext public
open import category-theory.natural-isomorphisms-maps-categories funext public
open import category-theory.natural-isomorphisms-maps-precategories funext public
open import category-theory.natural-numbers-object-precategories funext public
open import category-theory.natural-transformations-functors-categories funext public
open import category-theory.natural-transformations-functors-from-small-to-large-categories funext public
open import category-theory.natural-transformations-functors-from-small-to-large-precategories funext public
open import category-theory.natural-transformations-functors-large-categories funext public
open import category-theory.natural-transformations-functors-large-precategories funext public
open import category-theory.natural-transformations-functors-precategories funext public
open import category-theory.natural-transformations-maps-categories funext public
open import category-theory.natural-transformations-maps-from-small-to-large-precategories funext public
open import category-theory.natural-transformations-maps-precategories funext public
open import category-theory.nonunital-precategories funext public
open import category-theory.one-object-precategories funext public
open import category-theory.opposite-categories funext public
open import category-theory.opposite-large-precategories funext public
open import category-theory.opposite-precategories funext public
open import category-theory.opposite-preunivalent-categories funext public
open import category-theory.opposite-strongly-preunivalent-categories funext public
open import category-theory.pointed-endofunctors-categories funext public
open import category-theory.pointed-endofunctors-precategories funext public
open import category-theory.precategories funext public
open import category-theory.precategory-of-elements-of-a-presheaf funext public
open import category-theory.precategory-of-functors funext public
open import category-theory.precategory-of-functors-from-small-to-large-precategories funext public
open import category-theory.precategory-of-maps-from-small-to-large-precategories funext public
open import category-theory.precategory-of-maps-precategories funext public
open import category-theory.pregroupoids funext public
open import category-theory.presheaf-categories funext public
open import category-theory.preunivalent-categories funext public
open import category-theory.products-in-precategories funext public
open import category-theory.products-of-precategories funext public
open import category-theory.pseudomonic-functors-precategories funext public
open import category-theory.pullbacks-in-precategories funext public
open import category-theory.replete-subprecategories funext public
open import category-theory.representable-functors-categories funext public
open import category-theory.representable-functors-large-precategories funext public
open import category-theory.representable-functors-precategories funext public
open import category-theory.representing-arrow-category funext public
open import category-theory.restrictions-functors-cores-precategories funext public
open import category-theory.right-extensions-precategories funext public
open import category-theory.right-kan-extensions-precategories funext public
open import category-theory.rigid-objects-categories funext public
open import category-theory.rigid-objects-precategories funext public
open import category-theory.set-magmoids funext public
open import category-theory.sieves-in-categories funext public
open import category-theory.simplex-category funext public
open import category-theory.slice-precategories funext public
open import category-theory.split-essentially-surjective-functors-precategories funext public
open import category-theory.strict-categories funext public
open import category-theory.strongly-preunivalent-categories funext public
open import category-theory.structure-equivalences-set-magmoids funext public
open import category-theory.subcategories funext public
open import category-theory.subprecategories funext public
open import category-theory.subterminal-precategories funext public
open import category-theory.terminal-category funext public
open import category-theory.terminal-objects-precategories funext public
open import category-theory.wide-subcategories funext public
open import category-theory.wide-subprecategories funext public
open import category-theory.yoneda-lemma-categories funext public
open import category-theory.yoneda-lemma-precategories funext public
```
