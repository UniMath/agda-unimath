# Category theory

## Examples of categories and large categories

| Category          | File                                                                                                        |
| ----------------- | ----------------------------------------------------------------------------------------------------------- |
| Commutative Rings | [`commutative-algebra.category-of-commutative-rings`](commutative-algebra.category-of-commutative-rings.md) |
| Groups            | [`group-theory.category-of-groups`](group-theory.category-of-groups.md)                                     |
| Rings             | [`ring-theory.category-of-rings`](ring-theory.category-of-rings.md)                                         |
| Semigroups        | [`group-theory.category-of-semigroups`](group-theory.category-of-semigroups.md)                             |
| Sets              | [`foundation.category-of-sets`](foundation.category-of-sets.md)                                             |

## Examples of precategories and large precategories

| Precategory           | File                                                                                                                      |
| --------------------- | ------------------------------------------------------------------------------------------------------------------------- |
| Abelian groups        | [`group-theory.precategory-of-abelian-groups`](group-theory.precategory-of-abelian-groups.md)                             |
| Commutative monoids   | [`group-theory.precategory-of-commutative-monoids`](group-theory.precategory-of-commutative-monoids.md)                   |
| Commutative rings     | [`commutative-algebra.precategory-of-commutative-rings`](commutative-algebra.precategory-of-commutative-rings.md)         |
| Commutative semirings | [`commutative-algebra.precategory-of-commutative-semirings`](commutative-algebra.precategory-of-commutative-semirings.md) |
| Concrete groups       | [`group-theory.precategory-of-concrete-groups`](group-theory.precategory-of-concrete-groups.md)                           |
| Finite species        | [`species.precategory-of-finite-species`](species.precategory-of-finite-species.md)                                       |
| `G`-sets              | [`group-theory.precategory-of-group-actions`](group-theory.precategory-of-group-actions.md)                               |
| Groups                | [`group-theory.precategory-of-groups`](group-theory.precategory-of-groups.md)                                             |
| Monoids               | [`group-theory.precategory-of-monoids`](group-theory.precategory-of-monoids.md)                                           |
| Rings                 | [`ring-theory.precategory-of-rings`](ring-theory.precategory-of-rings.md)                                                 |
| Semigroups            | [`group-theory.precategory-of-semigroups`](group-theory.precategory-of-semigroups.md)                                     |
| Semirings             | [`ring-theory.precategory-of-semirings`](ring-theory.precategory-of-semirings.md)                                         |
| Sets                  | [`foundation.category-of-sets`](foundation.category-of-sets.md)                                                           |

## Files in the category theory folder

```agda
module category-theory where

open import category-theory.adjunctions-large-precategories public
open import category-theory.anafunctors-categories public
open import category-theory.anafunctors-precategories public
open import category-theory.categories public
open import category-theory.category-of-functors public
open import category-theory.category-of-functors-from-small-to-large-categories public
open import category-theory.category-of-maps-categories public
open import category-theory.category-of-maps-from-small-to-large-categories public
open import category-theory.commuting-squares-of-morphisms-in-large-precategories public
open import category-theory.commuting-squares-of-morphisms-in-precategories public
open import category-theory.coproducts-in-precategories public
open import category-theory.dependent-products-of-categories public
open import category-theory.dependent-products-of-precategories public
open import category-theory.discrete-categories public
open import category-theory.endomorphisms-in-categories public
open import category-theory.endomorphisms-in-precategories public
open import category-theory.epimorphisms-in-large-precategories public
open import category-theory.equivalences-of-categories public
open import category-theory.equivalences-of-large-precategories public
open import category-theory.equivalences-of-precategories public
open import category-theory.exponential-objects-precategories public
open import category-theory.faithful-functors-precategories public
open import category-theory.function-categories public
open import category-theory.function-precategories public
open import category-theory.functors-categories public
open import category-theory.functors-from-small-to-large-categories public
open import category-theory.functors-from-small-to-large-precategories public
open import category-theory.functors-large-precategories public
open import category-theory.functors-precategories public
open import category-theory.groupoids public
open import category-theory.homotopies-natural-transformations-large-precategories public
open import category-theory.initial-objects-large-categories public
open import category-theory.initial-objects-large-precategories public
open import category-theory.initial-objects-precategories public
open import category-theory.isomorphisms-in-categories public
open import category-theory.isomorphisms-in-large-categories public
open import category-theory.isomorphisms-in-large-precategories public
open import category-theory.isomorphisms-in-precategories public
open import category-theory.large-categories public
open import category-theory.large-precategories public
open import category-theory.maps-categories public
open import category-theory.maps-from-small-to-large-categories public
open import category-theory.maps-from-small-to-large-precategories public
open import category-theory.maps-precategories public
open import category-theory.monomorphisms-in-large-precategories public
open import category-theory.natural-isomorphisms-functors-categories public
open import category-theory.natural-isomorphisms-functors-large-precategories public
open import category-theory.natural-isomorphisms-functors-precategories public
open import category-theory.natural-isomorphisms-maps-categories public
open import category-theory.natural-isomorphisms-maps-precategories public
open import category-theory.natural-numbers-object-precategories public
open import category-theory.natural-transformations-functors-categories public
open import category-theory.natural-transformations-functors-from-small-to-large-precategories public
open import category-theory.natural-transformations-functors-large-precategories public
open import category-theory.natural-transformations-functors-precategories public
open import category-theory.natural-transformations-maps-categories public
open import category-theory.natural-transformations-maps-from-small-to-large-precategories public
open import category-theory.natural-transformations-maps-precategories public
open import category-theory.one-object-precategories public
open import category-theory.opposite-precategories public
open import category-theory.precategories public
open import category-theory.precategory-of-functors public
open import category-theory.precategory-of-functors-from-small-to-large-precategories public
open import category-theory.precategory-of-maps-from-small-to-large-precategories public
open import category-theory.precategory-of-maps-precategories public
open import category-theory.pregroupoids public
open import category-theory.presheaf-categories public
open import category-theory.products-in-precategories public
open import category-theory.products-of-precategories public
open import category-theory.pullbacks-in-precategories public
open import category-theory.representable-functors-categories public
open import category-theory.representable-functors-large-precategories public
open import category-theory.representable-functors-precategories public
open import category-theory.representing-arrow-category public
open import category-theory.sieves-in-categories public
open import category-theory.slice-precategories public
open import category-theory.subprecategories public
open import category-theory.terminal-objects-precategories public
open import category-theory.yoneda-lemma-categories public
open import category-theory.yoneda-lemma-precategories public
```
