# The precategory of algebras of an equational theory

```agda
module universal-algebra.precategory-of-algebras-of-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.identity-types

open import universal-algebra.signatures
open import universal-algebra.models-of-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.homomorphisms-of-algebras
```

</details>

## Idea

For any [signature](universal-algebra.signatures.md) `S` and
`S`-[theory](universal-algebra.algebraic-theories.md) `T`, there is a
[large precategory](category-theory.large-precategories.md) of
`T`-[algebras](universal-algebra.algebras-of-theories.md) and `T`-algebra
[homomorphisms](universal-algebra.homomorphisms-of-algebras.md).

## Definition

```agda
module _
  {l1 l2 : Level} (S : signature l1) (T : Theory S l2)
  where

  Algebra-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l3 l4 → l1 ⊔ l3 ⊔ l4)
  Algebra-Large-Precategory = make-Large-Precategory
    ( Algebra S T)
    ( set-hom-Algebra S T)
    ( λ {l3} {l4} {l5} {X} {Y} {Z} → comp-hom-Algebra S T X Y Z)
    ( λ {l} {X} → id-hom-Algebra S T X)
    ( associative-comp-hom-Algebra S T)
    ( left-unit-law-comp-hom-Algebra S T)
    ( right-unit-law-comp-hom-Algebra S T)
```
