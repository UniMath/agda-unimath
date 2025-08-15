# Isomorphisms of algebras of theories

```agda
module universal-algebra.isomorphisms-algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.large-categories
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.precategory-of-algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

We characterize
[isomorphisms](category-theory.isomorphisms-in-large-precategories.md) of
[algebras of theories](universal-algebra.precategory-of-algebras-of-theories.md).

```agda
module _
  { l1 : Level} ( S : signature l1)
  { l2 : Level} ( T : Theory S l2)
  where

  iso-Eq-Model-Signature :
    {l3 : Level} (A B : Algebra S T l3)
    (b : Eq-Model-Signature S (model-Algebra S T A) (model-Algebra S T B)) →
    iso-Large-Precategory (Algebra-Large-Precategory S T) A B
  pr1 (iso-Eq-Model-Signature A B b) = {!   !}
  pr1 (pr2 (iso-Eq-Model-Signature A B b)) = {!   !}
  pr1 (pr2 (pr2 (iso-Eq-Model-Signature A B b))) = {!   !}
  pr2 (pr2 (pr2 (iso-Eq-Model-Signature A B b))) = {!   !}

  id-iso-comp-htpy-Algebra :
    {l3 : Level} (A B : Algebra S T l3) →
    iso-eq-Large-Precategory (Algebra-Large-Precategory S T) A B ~
    {!   !} ∘ Eq-eq-Algebra S T A B
  id-iso-comp-htpy-Algebra A B = {!   !}
```
