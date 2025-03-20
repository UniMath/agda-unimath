# Π-decompositions of types into types in a subuniverse

```agda
open import foundation.function-extensionality-axiom

module
  foundation.pi-decompositions-subuniverse
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.pi-decompositions funext
open import foundation.subuniverses funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.propositions
```

</details>

## Idea

Consider a subuniverse `P` and a type `A` in `P`. A **Π-decomposition** of `A`
into types in `P` consists of a type `X` in `P` and a family `Y` of types in `P`
indexed over `X`, equipped with an equivalence

```text
  A ≃ Π X Y.
```

## Definition

### The predicate of being a Π-decomposition in a subuniverse

```agda
is-in-subuniverse-Π-Decomposition :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {A : UU l3} →
  Π-Decomposition l1 l1 A → UU (l1 ⊔ l2)
is-in-subuniverse-Π-Decomposition P D =
  ( is-in-subuniverse P (indexing-type-Π-Decomposition D)) ×
  ( ( x : indexing-type-Π-Decomposition D) →
    ( is-in-subuniverse P (cotype-Π-Decomposition D x)))
```

### Π-decompositions in a subuniverse

```agda
Π-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  type-subuniverse P → UU (lsuc l1 ⊔ l2)
Π-Decomposition-Subuniverse P A =
  Σ ( type-subuniverse P)
    ( λ X →
      Σ ( fam-subuniverse P (inclusion-subuniverse P X))
        ( λ Y →
          inclusion-subuniverse P A ≃
          Π ( inclusion-subuniverse P X)
            ( λ x → inclusion-subuniverse P (Y x))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  (D : Π-Decomposition-Subuniverse P A)
  where

  subuniverse-indexing-type-Π-Decomposition-Subuniverse : type-subuniverse P
  subuniverse-indexing-type-Π-Decomposition-Subuniverse = pr1 D

  indexing-type-Π-Decomposition-Subuniverse : UU l1
  indexing-type-Π-Decomposition-Subuniverse =
    inclusion-subuniverse P
      subuniverse-indexing-type-Π-Decomposition-Subuniverse

  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverse :
    type-Prop (P indexing-type-Π-Decomposition-Subuniverse)
  is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverse =
    pr2 subuniverse-indexing-type-Π-Decomposition-Subuniverse

  subuniverse-cotype-Π-Decomposition-Subuniverse :
    fam-subuniverse P indexing-type-Π-Decomposition-Subuniverse
  subuniverse-cotype-Π-Decomposition-Subuniverse = pr1 (pr2 D)

  cotype-Π-Decomposition-Subuniverse :
    (indexing-type-Π-Decomposition-Subuniverse → UU l1)
  cotype-Π-Decomposition-Subuniverse X =
    inclusion-subuniverse P (subuniverse-cotype-Π-Decomposition-Subuniverse X)

  is-in-subuniverse-cotype-Π-Decomposition-Subuniverse :
    ((x : indexing-type-Π-Decomposition-Subuniverse) →
    type-Prop (P (cotype-Π-Decomposition-Subuniverse x)))
  is-in-subuniverse-cotype-Π-Decomposition-Subuniverse x =
    pr2 (subuniverse-cotype-Π-Decomposition-Subuniverse x)

  matching-correspondence-Π-Decomposition-Subuniverse :
    inclusion-subuniverse P A ≃
    Π ( indexing-type-Π-Decomposition-Subuniverse)
      ( cotype-Π-Decomposition-Subuniverse)
  matching-correspondence-Π-Decomposition-Subuniverse = pr2 (pr2 D)
```

## Properties

### The type of Π-decompositions in a subuniverse is equivalent to the total space of `is-in-subuniverse-Π-Decomposition`

```agda
map-equiv-total-is-in-subuniverse-Π-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Π-Decomposition-Subuniverse P A →
  Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Π-Decomposition P)
map-equiv-total-is-in-subuniverse-Π-Decomposition P A D =
  ( indexing-type-Π-Decomposition-Subuniverse P A D ,
    ( cotype-Π-Decomposition-Subuniverse P A D ,
      matching-correspondence-Π-Decomposition-Subuniverse P A D)) ,
  ( is-in-subuniverse-indexing-type-Π-Decomposition-Subuniverse P A D ,
    is-in-subuniverse-cotype-Π-Decomposition-Subuniverse P A D)

map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
    ( is-in-subuniverse-Π-Decomposition P) →
  Π-Decomposition-Subuniverse P A
map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverse P A X =
  ( ( indexing-type-Π-Decomposition (pr1 X) , (pr1 (pr2 X))) ,
    ( (λ x → cotype-Π-Decomposition (pr1 X) x , pr2 (pr2 X) x) ,
      matching-correspondence-Π-Decomposition (pr1 X)))

equiv-total-is-in-subuniverse-Π-Decomposition :
  {l1 l2 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P) →
  ( Π-Decomposition-Subuniverse P A) ≃
  ( Σ ( Π-Decomposition l1 l1 (inclusion-subuniverse P A))
      ( is-in-subuniverse-Π-Decomposition P))
pr1 (equiv-total-is-in-subuniverse-Π-Decomposition P A) =
  map-equiv-total-is-in-subuniverse-Π-Decomposition P A
pr2 (equiv-total-is-in-subuniverse-Π-Decomposition P A) =
  is-equiv-is-invertible
    ( map-inv-equiv-Π-Decomposition-Π-Decomposition-Subuniverse P A)
    ( refl-htpy)
    ( refl-htpy)
```
