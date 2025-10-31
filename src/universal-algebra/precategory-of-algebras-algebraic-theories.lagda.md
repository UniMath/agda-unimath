# The precategory of algebras of an algebraic theory

```agda
module universal-algebra.precategory-of-algebras-algebraic-theories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.identity-types

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-algebraic-theories
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

Given an [algebraic theory](universal-algebra.algebraic-theories.md) `T` over a
[signature](universal-algebra.signatures.md) `σ`, we have the
{{#concept "large precategory of `T`-algebras" Disambiguation="of an algebraic theory, single-sorted, finitary" Agda=Algebra-Large-Precategory}},
which consists of
`T`-[algebras](universal-algebra.algebras-of-algebraic-theories.md) and
`T`-[algebra homomorphisms](universal-algebra.homomorphisms-of-algebras.md).

## Definition

### The large precategory of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Algebraic-Theory l2 σ)
  where

  Algebra-Large-Precategory :
    Large-Precategory (λ l → l1 ⊔ l2 ⊔ lsuc l) (λ l3 l4 → l1 ⊔ l3 ⊔ l4)
  Algebra-Large-Precategory =
    make-Large-Precategory
      ( λ l → Algebra l σ T)
      ( set-hom-Algebra σ T)
      ( λ {l3} {l4} {l5} {X} {Y} {Z} → comp-hom-Algebra σ T X Y Z)
      ( λ {l} {X} → id-hom-Algebra σ T X)
      ( λ {l3} {l4} {l5} {l6} {X} {Y} {Z} {W} →
        associative-comp-hom-Algebra σ T X Y Z W)
      ( λ {l3} {l4} {X} {Y} → left-unit-law-comp-hom-Algebra σ T X Y)
      ( λ {l3} {l4} {X} {Y} → right-unit-law-comp-hom-Algebra σ T X Y)
```

### The small precategory of algebras

```agda
module _
  {l1 l2 : Level} (σ : signature l1) (T : Algebraic-Theory l2 σ)
  where

  Algebra-Precategory : (l3 : Level) → Precategory (l1 ⊔ l2 ⊔ lsuc l3) (l1 ⊔ l3)
  Algebra-Precategory =
    precategory-Large-Precategory (Algebra-Large-Precategory σ T)
```

## See also

- [The category of algebras of an equational theory](universal-algebra.category-of-algebras-algebraic-theories.md)
