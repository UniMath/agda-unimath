# Trees

```agda
{-# OPTIONS --guardedness #-}
```

## Files in the `trees` module

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import trees.algebras-polynomial-endofunctors funext univalence public
open import trees.bases-directed-trees funext univalence truncations public
open import trees.bases-enriched-directed-trees funext univalence truncations public
open import trees.binary-w-types public
open import trees.bounded-multisets funext univalence truncations public
open import trees.coalgebra-of-directed-trees funext univalence truncations public
open import trees.coalgebra-of-enriched-directed-trees funext univalence truncations public
open import trees.coalgebras-polynomial-endofunctors funext univalence public
open import trees.combinator-directed-trees funext univalence truncations public
open import trees.combinator-enriched-directed-trees funext univalence truncations public
open import trees.directed-trees funext univalence truncations public
open import trees.elementhood-relation-coalgebras-polynomial-endofunctors funext univalence truncations public
open import trees.elementhood-relation-w-types funext univalence truncations public
open import trees.empty-multisets funext univalence truncations public
open import trees.enriched-directed-trees funext univalence truncations public
open import trees.equivalences-directed-trees funext univalence truncations public
open import trees.equivalences-enriched-directed-trees funext univalence truncations public
open import trees.extensional-w-types funext univalence truncations public
open import trees.fibers-directed-trees funext univalence truncations public
open import trees.fibers-enriched-directed-trees funext univalence truncations public
open import trees.full-binary-trees funext univalence truncations public
open import trees.functoriality-combinator-directed-trees funext univalence truncations public
open import trees.functoriality-fiber-directed-tree funext univalence truncations public
open import trees.functoriality-w-types funext univalence truncations public
open import trees.hereditary-w-types funext public
open import trees.indexed-w-types public
open import trees.induction-w-types funext univalence truncations public
open import trees.inequality-w-types funext univalence truncations public
open import trees.lower-types-w-types funext univalence truncations public
open import trees.morphisms-algebras-polynomial-endofunctors funext univalence truncations public
open import trees.morphisms-coalgebras-polynomial-endofunctors funext univalence truncations public
open import trees.morphisms-directed-trees funext univalence truncations public
open import trees.morphisms-enriched-directed-trees funext univalence truncations public
open import trees.multiset-indexed-dependent-products-of-types funext univalence truncations public
open import trees.multisets funext univalence truncations public
open import trees.planar-binary-trees funext univalence truncations public
open import trees.plane-trees funext univalence truncations public
open import trees.polynomial-endofunctors funext univalence public
open import trees.raising-universe-levels-directed-trees funext univalence truncations public
open import trees.ranks-of-elements-w-types funext univalence truncations public
open import trees.rooted-morphisms-directed-trees funext univalence truncations public
open import trees.rooted-morphisms-enriched-directed-trees funext univalence truncations public
open import trees.rooted-quasitrees funext univalence truncations public
open import trees.rooted-undirected-trees funext univalence truncations public
open import trees.small-multisets funext univalence truncations public
open import trees.submultisets funext univalence truncations public
open import trees.transitive-multisets funext univalence truncations public
open import trees.underlying-trees-elements-coalgebras-polynomial-endofunctors funext univalence truncations public
open import trees.underlying-trees-of-elements-of-w-types funext univalence truncations public
open import trees.undirected-trees funext univalence truncations public
open import trees.universal-multiset funext univalence truncations public
open import trees.universal-tree public
open import trees.w-type-of-natural-numbers funext univalence truncations public
open import trees.w-type-of-propositions funext univalence truncations public
open import trees.w-types funext univalence truncations public
```
