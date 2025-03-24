# Lists

## Modules in the lists namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module lists
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import lists.arrays funext univalence truncations public
open import lists.concatenation-lists funext univalence truncations public
open import lists.equality-lists funext univalence truncations public
open import lists.flattening-lists funext univalence truncations public
open import lists.functoriality-lists funext univalence truncations public
open import lists.lists public
open import lists.lists-discrete-types funext univalence truncations public
open import lists.permutation-lists funext univalence truncations public
open import lists.permutation-vectors funext univalence truncations public
open import lists.predicates-on-lists funext univalence public
open import lists.quicksort-lists funext univalence truncations public
open import lists.reversing-lists funext univalence truncations public
open import lists.sort-by-insertion-lists funext univalence truncations public
open import lists.sort-by-insertion-vectors funext univalence truncations public
open import lists.sorted-lists funext univalence truncations public
open import lists.sorted-vectors funext univalence truncations public
open import lists.sorting-algorithms-lists funext univalence truncations public
open import lists.sorting-algorithms-vectors funext univalence truncations public
open import lists.universal-property-lists-wild-monoids funext univalence truncations public
```
