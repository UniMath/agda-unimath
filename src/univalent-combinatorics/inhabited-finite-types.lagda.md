# Inhabited finite types

```agda
module univalent-combinatorics.inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

An **inhabited finite type** is a
[finite type](univalent-combinatorics.finite-types.md) that is
[inhabited](foundation.inhabited-types.md), meaning it is a type that is
[merely equivalent](foundation.mere-equivalences.md) to a
[standard finite type](univalent-combinatorics.standard-finite-types.md), and
that comes equipped with a term of its
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### Inhabited finite types

```agda
Inhabited-Finite-Type : (l : Level) → UU (lsuc l)
Inhabited-Finite-Type l =
  Σ (Finite-Type l) (λ X → is-inhabited (type-Finite-Type X))

module _
  {l : Level} (X : Inhabited-Finite-Type l)
  where

  finite-type-Inhabited-Finite-Type : Finite-Type l
  finite-type-Inhabited-Finite-Type = pr1 X

  type-Inhabited-Finite-Type : UU l
  type-Inhabited-Finite-Type =
    type-Finite-Type finite-type-Inhabited-Finite-Type

  is-finite-Inhabited-Finite-Type : is-finite type-Inhabited-Finite-Type
  is-finite-Inhabited-Finite-Type =
    is-finite-type-Finite-Type finite-type-Inhabited-Finite-Type

  is-inhabited-type-Inhabited-Finite-Type :
    is-inhabited type-Inhabited-Finite-Type
  is-inhabited-type-Inhabited-Finite-Type = pr2 X

  inhabited-type-Inhabited-Finite-Type : Inhabited-Type l
  pr1 inhabited-type-Inhabited-Finite-Type = type-Inhabited-Finite-Type
  pr2 inhabited-type-Inhabited-Finite-Type =
    is-inhabited-type-Inhabited-Finite-Type

compute-Inhabited-Finite-Type :
  {l : Level} →
  Inhabited-Finite-Type l ≃
  Σ (Inhabited-Type l) (λ X → is-finite (type-Inhabited-Type X))
compute-Inhabited-Finite-Type = equiv-right-swap-Σ

is-finite-and-inhabited-Prop : {l : Level} → UU l → Prop l
is-finite-and-inhabited-Prop X =
  product-Prop (is-finite-Prop X) (is-inhabited-Prop X)

is-finite-and-inhabited : {l : Level} → UU l → UU l
is-finite-and-inhabited X =
  type-Prop (is-finite-and-inhabited-Prop X)

compute-Inhabited-Finite-Type' :
  {l : Level} →
  Inhabited-Finite-Type l ≃ type-subuniverse is-finite-and-inhabited-Prop
compute-Inhabited-Finite-Type' = associative-Σ _ _ _

map-compute-Inhabited-Finite-Type' :
  {l : Level} →
  Inhabited-Finite-Type l → type-subuniverse is-finite-and-inhabited-Prop
map-compute-Inhabited-Finite-Type' = map-associative-Σ _ _ _

map-inv-compute-Inhabited-Finite-Type' :
  {l : Level} →
  type-subuniverse is-finite-and-inhabited-Prop → Inhabited-Finite-Type l
map-inv-compute-Inhabited-Finite-Type' = map-inv-associative-Σ _ _ _
```

### Families of inhabited types

```agda
Family-Of-Inhabited-Finite-Types :
  {l1 : Level} → (l2 : Level) → (X : Finite-Type l1) → UU (l1 ⊔ lsuc l2)
Family-Of-Inhabited-Finite-Types l2 X =
  type-Finite-Type X → Inhabited-Finite-Type l2

module _
  {l1 l2 : Level} (X : Finite-Type l1)
  (Y : Family-Of-Inhabited-Finite-Types l2 X)
  where

  type-Family-Of-Inhabited-Finite-Types : type-Finite-Type X → UU l2
  type-Family-Of-Inhabited-Finite-Types x = type-Inhabited-Finite-Type (Y x)

  finite-type-Family-Of-Inhabited-Finite-Types :
    type-Finite-Type X → Finite-Type l2
  pr1 (finite-type-Family-Of-Inhabited-Finite-Types x) =
    type-Family-Of-Inhabited-Finite-Types x
  pr2 (finite-type-Family-Of-Inhabited-Finite-Types x) =
    is-finite-Inhabited-Finite-Type (Y x)

  is-inhabited-type-Family-Of-Inhabited-Finite-Types :
    (x : type-Finite-Type X) →
    is-inhabited (type-Family-Of-Inhabited-Finite-Types x)
  is-inhabited-type-Family-Of-Inhabited-Finite-Types x =
    is-inhabited-type-Inhabited-Finite-Type (Y x)

  total-Family-Of-Inhabited-Finite-Types : Finite-Type (l1 ⊔ l2)
  total-Family-Of-Inhabited-Finite-Types =
    Σ-Finite-Type X finite-type-Family-Of-Inhabited-Finite-Types

compute-Fam-Inhabited-Finite-Type :
  {l1 l2 : Level} → (X : Finite-Type l1) →
  Family-Of-Inhabited-Finite-Types l2 X ≃
  Σ ( Fam-Inhabited-Types l2 (type-Finite-Type X))
    ( λ Y → (x : type-Finite-Type X) → is-finite (type-Inhabited-Type (Y x)))
compute-Fam-Inhabited-Finite-Type X =
  ( distributive-Π-Σ) ∘e
  ( equiv-Π
    ( λ _ → Σ (Inhabited-Type _) (is-finite ∘ type-Inhabited-Type))
    ( id-equiv)
    ( λ _ → compute-Inhabited-Finite-Type))
```

## Proposition

### Equality in inhabited finite types

```agda
equiv-Inhabited-Finite-Type :
  {l1 l2 : Level} → Inhabited-Finite-Type l1 → Inhabited-Finite-Type l2 →
  UU (l1 ⊔ l2)
equiv-Inhabited-Finite-Type X Y =
  type-Inhabited-Finite-Type X ≃ type-Inhabited-Finite-Type Y

eq-equiv-Inhabited-Finite-Type :
  {l : Level} → (X Y : Inhabited-Finite-Type l) →
  equiv-Inhabited-Finite-Type X Y → X ＝ Y
eq-equiv-Inhabited-Finite-Type X Y e =
  eq-type-subtype
    ( λ X → is-inhabited-Prop (type-Finite-Type X))
    ( eq-equiv-Finite-Type
      ( finite-type-Inhabited-Finite-Type X)
      ( finite-type-Inhabited-Finite-Type Y)
      ( e))
```

### Every type in `Type-With-Cardinality-ℕ (succ-ℕ n)` is an inhabited finite type

```agda
is-finite-and-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ :
  {l : Level} → (n : ℕ) → (F : Type-With-Cardinality-ℕ l (succ-ℕ n)) →
  is-finite-and-inhabited (type-Type-With-Cardinality-ℕ (succ-ℕ n) F)
pr1 (is-finite-and-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ n F) =
  is-finite-type-Type-With-Cardinality-ℕ (succ-ℕ n) F
pr2 (is-finite-and-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ n F) =
  is-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ n F
```
