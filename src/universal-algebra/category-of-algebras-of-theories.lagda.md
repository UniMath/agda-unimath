# The category of algebras of theories

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.category-of-algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.large-categories
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.isomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.precategory-of-algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

The
[precategory of algebras of a theory](universal-algebra.precategory-of-algebras-of-theories.md)
is a [category](category-theory.large-categories.md).

## Definition

```agda
module _
  {l1 l2 : Level} (S : signature l1) (T : Theory S l2)
  where

  is-large-category-Algebra-Large-Precategory :
    is-large-category-Large-Precategory (Algebra-Large-Precategory S T)
  is-large-category-Algebra-Large-Precategory = is-equiv-iso-eq-Algebra S T

  Algebra-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l3 → _⊔_ (l1 ⊔ l3))
  large-precategory-Large-Category Algebra-Large-Category =
    Algebra-Large-Precategory S T
  is-large-category-Large-Category Algebra-Large-Category =
    is-large-category-Algebra-Large-Precategory
```
