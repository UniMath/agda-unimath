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
[inhabited](foundation.inhabited-types.md), meaning it is a type that is merely
equivalent to a standard finite type, and that comes equipped with a term of its
propositional truncation.

## Definitions

### Inhabited finite types

```agda
Inhabited-𝔽 : (l : Level) → UU (lsuc l)
Inhabited-𝔽 l = Σ (𝔽 l) (λ X → is-inhabited (type-𝔽 X))

module _
  {l : Level} (X : Inhabited-𝔽 l)
  where

  finite-type-Inhabited-𝔽 : 𝔽 l
  finite-type-Inhabited-𝔽 = pr1 X

  type-Inhabited-𝔽 : UU l
  type-Inhabited-𝔽 = type-𝔽 finite-type-Inhabited-𝔽

  is-finite-Inhabited-𝔽 : is-finite type-Inhabited-𝔽
  is-finite-Inhabited-𝔽 = is-finite-type-𝔽 finite-type-Inhabited-𝔽

  is-inhabited-type-Inhabited-𝔽 : is-inhabited type-Inhabited-𝔽
  is-inhabited-type-Inhabited-𝔽 = pr2 X

  inhabited-type-Inhabited-𝔽 : Inhabited-Type l
  pr1 inhabited-type-Inhabited-𝔽 = type-Inhabited-𝔽
  pr2 inhabited-type-Inhabited-𝔽 = is-inhabited-type-Inhabited-𝔽

compute-Inhabited-𝔽 :
  {l : Level} →
  Inhabited-𝔽 l ≃
    Σ (Inhabited-Type l) (λ X → is-finite (type-Inhabited-Type X))
compute-Inhabited-𝔽 = equiv-right-swap-Σ

is-finite-and-inhabited-Prop : {l : Level} → UU l → Prop l
is-finite-and-inhabited-Prop X =
  prod-Prop (is-finite-Prop X) (is-inhabited-Prop X)

is-finite-and-inhabited : {l : Level} → UU l → UU l
is-finite-and-inhabited X =
  type-Prop (is-finite-and-inhabited-Prop X)

compute-Inhabited-𝔽' :
  {l : Level} →
  Inhabited-𝔽 l ≃ type-subuniverse is-finite-and-inhabited-Prop
compute-Inhabited-𝔽' = associative-Σ _ _ _

map-compute-Inhabited-𝔽' :
  {l : Level} →
  Inhabited-𝔽 l → type-subuniverse is-finite-and-inhabited-Prop
map-compute-Inhabited-𝔽' = map-associative-Σ _ _ _

map-inv-compute-Inhabited-𝔽' :
  {l : Level} →
  type-subuniverse is-finite-and-inhabited-Prop → Inhabited-𝔽 l
map-inv-compute-Inhabited-𝔽' = map-inv-associative-Σ _ _ _
```

### Families of inhabited types

```agda
Fam-Inhabited-Types-𝔽 :
  {l1 : Level} → (l2 : Level) → (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types-𝔽 l2 X = type-𝔽 X → Inhabited-𝔽 l2

module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : Fam-Inhabited-Types-𝔽 l2 X)
  where

  type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → UU l2
  type-Fam-Inhabited-Types-𝔽 x = type-Inhabited-𝔽 (Y x)

  finite-type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → 𝔽 l2
  pr1 (finite-type-Fam-Inhabited-Types-𝔽 x) = type-Fam-Inhabited-Types-𝔽 x
  pr2 (finite-type-Fam-Inhabited-Types-𝔽 x) = is-finite-Inhabited-𝔽 (Y x)

  is-inhabited-type-Fam-Inhabited-Types-𝔽 :
    (x : type-𝔽 X) → is-inhabited (type-Fam-Inhabited-Types-𝔽 x)
  is-inhabited-type-Fam-Inhabited-Types-𝔽 x =
    is-inhabited-type-Inhabited-𝔽 (Y x)

  total-Fam-Inhabited-Types-𝔽 : 𝔽 (l1 ⊔ l2)
  total-Fam-Inhabited-Types-𝔽 = Σ-𝔽 X finite-type-Fam-Inhabited-Types-𝔽

compute-Fam-Inhabited-𝔽 :
  {l1 l2 : Level} → (X : 𝔽 l1) →
  Fam-Inhabited-Types-𝔽 l2 X ≃
    Σ ( Fam-Inhabited-Types l2 (type-𝔽 X))
      ( λ Y → ((x : (type-𝔽 X)) → is-finite (type-Inhabited-Type (Y x))))
compute-Fam-Inhabited-𝔽 X =
  ( distributive-Π-Σ) ∘e
  ( equiv-Π
    ( λ _ → Σ (Inhabited-Type _) (is-finite ∘ type-Inhabited-Type))
    ( id-equiv)
    ( λ _ → compute-Inhabited-𝔽))
```

## Proposition

### Equality in inhabited finite types

```agda
eq-equiv-Inhabited-𝔽 :
  {l : Level} → (X Y : Inhabited-𝔽 l) →
  type-Inhabited-𝔽 X ≃ type-Inhabited-𝔽 Y → X ＝ Y
eq-equiv-Inhabited-𝔽 X Y e =
  eq-type-subtype
    ( λ X → is-inhabited-Prop (type-𝔽 X))
    ( eq-equiv-𝔽
      ( finite-type-Inhabited-𝔽 X)
      ( finite-type-Inhabited-𝔽 Y)
      ( e))
```

### Every type in `UU-Fin (succ-ℕ n)` is a inhabited finite type

```agda
is-finite-and-inhabited-type-UU-Fin-succ-ℕ :
  {l : Level} → (n : ℕ) → (F : UU-Fin l (succ-ℕ n)) →
  is-finite-and-inhabited (type-UU-Fin (succ-ℕ n) F)
pr1 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) =
  is-finite-type-UU-Fin (succ-ℕ n) F
pr2 (is-finite-and-inhabited-type-UU-Fin-succ-ℕ n F) =
  is-inhabited-type-UU-Fin-succ-ℕ n F
```
