# Subterminal precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.subterminal-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets funext
open import category-theory.fully-faithful-functors-precategories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext
open import category-theory.pregroupoids funext
open import category-theory.strict-categories funext
open import category-theory.terminal-category funext

open import foundation.action-on-identifications-functions
open import foundation.contractible-types funext
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.iterated-dependent-product-types funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A [precategory](category-theory.precategories.md) is **subterminal** if its
[terminal projection functor](category-theory.terminal-category.md) is
[fully faithful](category-theory.fully-faithful-functors-precategories.md).

## Definitions

### The predicate on precategories of being subterminal

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-subterminal-Precategory : UU (l1 ⊔ l2)
  is-subterminal-Precategory =
    is-fully-faithful-functor-Precategory C terminal-Precategory
      ( terminal-functor-Precategory C)

  is-subterminal-prop-Precategory : Prop (l1 ⊔ l2)
  is-subterminal-prop-Precategory =
    is-fully-faithful-prop-functor-Precategory C terminal-Precategory
      ( terminal-functor-Precategory C)

  is-prop-is-subterminal-Precategory : is-prop is-subterminal-Precategory
  is-prop-is-subterminal-Precategory =
    is-prop-is-fully-faithful-functor-Precategory C terminal-Precategory
      ( terminal-functor-Precategory C)
```
