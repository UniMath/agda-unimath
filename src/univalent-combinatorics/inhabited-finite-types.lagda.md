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
Inhabited-Finite-Type l = Σ (𝔽 l) (λ X → is-inhabited (type-𝔽 X))

module _
  {l : Level} (X : Inhabited-Finite-Type l)
  where

  finite-type-Inhabited-Finite-Type : 𝔽 l
  finite-type-Inhabited-Finite-Type = pr1 X

  type-Inhabited-Finite-Type : UU l
  type-Inhabited-Finite-Type = type-𝔽 finite-type-Inhabited-Finite-Type

  is-finite-Inhabited-Finite-Type : is-finite type-Inhabited-Finite-Type
  is-finite-Inhabited-Finite-Type = is-finite-type-𝔽 finite-type-Inhabited-Finite-Type

  is-inhabited-type-Inhabited-Finite-Type : is-inhabited type-Inhabited-Finite-Type
  is-inhabited-type-Inhabited-Finite-Type = pr2 X

  inhabited-type-Inhabited-Finite-Type : Inhabited-Type l
  pr1 inhabited-type-Inhabited-Finite-Type = type-Inhabited-Finite-Type
  pr2 inhabited-type-Inhabited-Finite-Type = is-inhabited-type-Inhabited-Finite-Type

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
Fam-Inhabited-Types-𝔽 :
  {l1 : Level} → (l2 : Level) → (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types-𝔽 l2 X = type-𝔽 X → Inhabited-Finite-Type l2

module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : Fam-Inhabited-Types-𝔽 l2 X)
  where

  type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → UU l2
  type-Fam-Inhabited-Types-𝔽 x = type-Inhabited-Finite-Type (Y x)

  finite-type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → 𝔽 l2
  pr1 (finite-type-Fam-Inhabited-Types-𝔽 x) = type-Fam-Inhabited-Types-𝔽 x
  pr2 (finite-type-Fam-Inhabited-Types-𝔽 x) = is-finite-Inhabited-Finite-Type (Y x)

  is-inhabited-type-Fam-Inhabited-Types-𝔽 :
    (x : type-𝔽 X) → is-inhabited (type-Fam-Inhabited-Types-𝔽 x)
  is-inhabited-type-Fam-Inhabited-Types-𝔽 x =
    is-inhabited-type-Inhabited-Finite-Type (Y x)

  total-Fam-Inhabited-Types-𝔽 : 𝔽 (l1 ⊔ l2)
  total-Fam-Inhabited-Types-𝔽 = Σ-𝔽 X finite-type-Fam-Inhabited-Types-𝔽

compute-Fam-Inhabited-Finite-Type :
  {l1 l2 : Level} → (X : 𝔽 l1) →
  Fam-Inhabited-Types-𝔽 l2 X ≃
  Σ ( Fam-Inhabited-Types l2 (type-𝔽 X))
    ( λ Y → (x : type-𝔽 X) → is-finite (type-Inhabited-Type (Y x)))
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
eq-equiv-Inhabited-Finite-Type :
  {l : Level} → (X Y : Inhabited-Finite-Type l) →
  type-Inhabited-Finite-Type X ≃ type-Inhabited-Finite-Type Y → X ＝ Y
eq-equiv-Inhabited-Finite-Type X Y e =
  eq-type-subtype
    ( λ X → is-inhabited-Prop (type-𝔽 X))
    ( eq-equiv-𝔽
      ( finite-type-Inhabited-Finite-Type X)
      ( finite-type-Inhabited-Finite-Type Y)
      ( e))
```

### Every type in `UU-Fin (succ-ℕ n)` is an inhabited finite type

```agda
is-finite-and-inhabited-type-UU-Fin-succ-ℕ :
  {l : Level} → (n : ℕ) → (F : UU-Fin l (succ-ℕ n)) →
  is-finite-and-inhabited (type-UU-Fin (succ-ℕ n) F)
pr1 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) =
  is-finite-type-UU-Fin (succ-ℕ n) F
pr2 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) =
  is-inhabited-type-UU-Fin-succ-ℕ n F
```
