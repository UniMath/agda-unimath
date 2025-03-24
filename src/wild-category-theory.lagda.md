# Wild category theory

```agda
{-# OPTIONS --guardedness #-}
```

## Instances of wild categories

{{#include tables/wild-categories.md}}

## Modules in the wild category theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module wild-category-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import wild-category-theory.coinductive-isomorphisms-in-noncoherent-large-omega-precategories funext univalence truncations public
open import wild-category-theory.coinductive-isomorphisms-in-noncoherent-omega-precategories funext univalence truncations public
open import wild-category-theory.colax-functors-noncoherent-large-omega-precategories funext univalence truncations public
open import wild-category-theory.colax-functors-noncoherent-omega-precategories funext univalence truncations public
open import wild-category-theory.maps-noncoherent-large-omega-precategories funext univalence truncations public
open import wild-category-theory.maps-noncoherent-omega-precategories funext univalence truncations public
open import wild-category-theory.noncoherent-large-omega-precategories funext univalence truncations public
open import wild-category-theory.noncoherent-omega-precategories funext univalence truncations public
```
