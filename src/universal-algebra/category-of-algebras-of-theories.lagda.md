# The category of algebras of an equational theory

```agda
{-# OPTIONS --lossy-unification #-}

module universal-algebra.category-of-algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
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

Given a [theory](universal-algebra.algebraic-theories.md) `T` over a
[signature](universal-algebra.signatures.md) `σ`, we have the
{{#concept "large category of `T`-algebras" Disambiguation="of an equational theory over a signature" Agda=Algebra-Large-Category}},
which consists of `T`-[algebras](universal-algebra.algebras-of-theories.md) and
`T`-[algebra homomorphisms](universal-algebra.homomorphisms-of-algebras.md).

## Definition

### The large category of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Theory σ l2)
  where

  is-large-category-Algebra-Large-Precategory :
    is-large-category-Large-Precategory (Algebra-Large-Precategory σ T)
  is-large-category-Algebra-Large-Precategory = is-equiv-iso-eq-Algebra σ T

  Algebra-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l3 → _⊔_ (l1 ⊔ l3))
  large-precategory-Large-Category Algebra-Large-Category =
    Algebra-Large-Precategory σ T
  is-large-category-Large-Category Algebra-Large-Category =
    is-large-category-Algebra-Large-Precategory
```

### The small category of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Theory σ l2)
  where

  Algebra-Category : (l3 : Level) → Category (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
  Algebra-Category =
    category-Large-Category (Algebra-Large-Category σ T)
```
