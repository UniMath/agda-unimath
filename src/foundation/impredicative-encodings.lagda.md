# Impredicative encodings of the logical operations

```agda
open import foundation.function-extensionality-axiom

module
  foundation.impredicative-encodings
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.disjunction funext
open import foundation.empty-types funext
open import foundation.existential-quantification funext
open import foundation.homotopies funext
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.propositional-truncations funext
open import foundation.universal-quantification funext
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

By universally quantifying over all
[propositions](foundation-core.propositions.md) in a universe, we can define all
the logical operations. The idea is to use the fact that any proposition `P` is
[equivalent](foundation.logical-equivalences.md) to the proposition
`(Q : Prop l) → (P ⇒ Q) ⇒ Q`, which can be thought of as the least proposition
`Q` containing `P`.

### The impredicative encoding of the propositional truncation

```agda
module _
  {l : Level} (A : UU l)
  where

  impredicative-trunc-Prop : Prop (lsuc l)
  impredicative-trunc-Prop =
    ∀' (Prop l) (λ Q → function-Prop (A → type-Prop Q) Q)

  type-impredicative-trunc-Prop : UU (lsuc l)
  type-impredicative-trunc-Prop =
    type-Prop impredicative-trunc-Prop

  map-impredicative-trunc-Prop :
    type-trunc-Prop A → type-impredicative-trunc-Prop
  map-impredicative-trunc-Prop =
    map-universal-property-trunc-Prop
      ( impredicative-trunc-Prop)
      ( λ x Q f → f x)

  map-inv-impredicative-trunc-Prop :
    type-impredicative-trunc-Prop → type-trunc-Prop A
  map-inv-impredicative-trunc-Prop H =
    H (trunc-Prop A) unit-trunc-Prop

  equiv-impredicative-trunc-Prop :
    type-trunc-Prop A ≃ type-impredicative-trunc-Prop
  equiv-impredicative-trunc-Prop =
    equiv-iff
      ( trunc-Prop A)
      ( impredicative-trunc-Prop)
      ( map-impredicative-trunc-Prop)
      ( map-inv-impredicative-trunc-Prop)
```

### The impredicative encoding of conjunction

```agda
module _
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2)
  where

  impredicative-conjunction-Prop : Prop (lsuc (l1 ⊔ l2))
  impredicative-conjunction-Prop =
    ∀' (Prop (l1 ⊔ l2)) (λ Q → (P1 ⇒ P2 ⇒ Q) ⇒ Q)

  type-impredicative-conjunction-Prop : UU (lsuc (l1 ⊔ l2))
  type-impredicative-conjunction-Prop =
    type-Prop impredicative-conjunction-Prop

  map-product-impredicative-conjunction-Prop :
    type-conjunction-Prop P1 P2 → type-impredicative-conjunction-Prop
  map-product-impredicative-conjunction-Prop (p1 , p2) Q f = f p1 p2

  map-inv-product-impredicative-conjunction-Prop :
    type-impredicative-conjunction-Prop → type-conjunction-Prop P1 P2
  map-inv-product-impredicative-conjunction-Prop H = H (P1 ∧ P2) pair

  equiv-product-impredicative-conjunction-Prop :
    type-conjunction-Prop P1 P2 ≃ type-impredicative-conjunction-Prop
  equiv-product-impredicative-conjunction-Prop =
    equiv-iff
      ( P1 ∧ P2)
      ( impredicative-conjunction-Prop)
      ( map-product-impredicative-conjunction-Prop)
      ( map-inv-product-impredicative-conjunction-Prop)
```

### The impredicative encoding of disjunction

```agda
module _
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2)
  where

  impredicative-disjunction-Prop : Prop (lsuc (l1 ⊔ l2))
  impredicative-disjunction-Prop =
    ∀' (Prop (l1 ⊔ l2)) (λ Q → (P1 ⇒ Q) ⇒ (P2 ⇒ Q) ⇒ Q)

  type-impredicative-disjunction-Prop : UU (lsuc (l1 ⊔ l2))
  type-impredicative-disjunction-Prop =
    type-Prop impredicative-disjunction-Prop

  map-impredicative-disjunction-Prop :
    type-disjunction-Prop P1 P2 → type-impredicative-disjunction-Prop
  map-impredicative-disjunction-Prop =
    map-universal-property-trunc-Prop
      ( impredicative-disjunction-Prop)
      ( rec-coproduct (λ x Q f1 f2 → f1 x) (λ y Q f1 f2 → f2 y))

  map-inv-impredicative-disjunction-Prop :
    type-impredicative-disjunction-Prop → type-disjunction-Prop P1 P2
  map-inv-impredicative-disjunction-Prop H =
    H (P1 ∨ P2) (inl-disjunction) (inr-disjunction)

  equiv-impredicative-disjunction-Prop :
    type-disjunction-Prop P1 P2 ≃ type-impredicative-disjunction-Prop
  equiv-impredicative-disjunction-Prop =
    equiv-iff
      ( P1 ∨ P2)
      ( impredicative-disjunction-Prop)
      ( map-impredicative-disjunction-Prop)
      ( map-inv-impredicative-disjunction-Prop)
```

### The impredicative encoding of the empty type

```agda
impredicative-empty-Prop : Prop (lsuc lzero)
impredicative-empty-Prop = ∀' (Prop lzero) (λ P → P)

type-impredicative-empty-Prop : UU (lsuc lzero)
type-impredicative-empty-Prop = type-Prop impredicative-empty-Prop

is-empty-impredicative-empty-Prop :
  is-empty type-impredicative-empty-Prop
is-empty-impredicative-empty-Prop e = e empty-Prop

equiv-impredicative-empty-Prop :
  empty ≃ type-impredicative-empty-Prop
equiv-impredicative-empty-Prop =
  equiv-is-empty id is-empty-impredicative-empty-Prop
```

### The impredicative encoding of negation

```agda
module _
  {l : Level} (A : UU l)
  where

  impredicative-neg-Prop : Prop (lsuc l)
  impredicative-neg-Prop =
    Π-Prop (Prop l) (λ Q → function-Prop A Q)

  type-impredicative-neg-Prop : UU (lsuc l)
  type-impredicative-neg-Prop = type-Prop impredicative-neg-Prop

  map-impredicative-neg-Prop : ¬ A → type-impredicative-neg-Prop
  map-impredicative-neg-Prop f Q a = ex-falso (f a)

  map-inv-impredicative-neg-Prop : type-impredicative-neg-Prop → ¬ A
  map-inv-impredicative-neg-Prop H a = H (neg-type-Prop A) a a

  equiv-impredicative-neg-Prop : ¬ A ≃ type-impredicative-neg-Prop
  equiv-impredicative-neg-Prop =
    equiv-iff
      ( neg-type-Prop A)
      ( impredicative-neg-Prop)
      ( map-impredicative-neg-Prop)
      ( map-inv-impredicative-neg-Prop)
```

### The impredicative encoding of existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2)
  where

  impredicative-exists-Prop : Prop (lsuc (l1 ⊔ l2))
  impredicative-exists-Prop =
    ∀' (Prop (l1 ⊔ l2)) (λ Q → (∀' A (λ x → P x ⇒ Q)) ⇒ Q)

  type-impredicative-exists-Prop : UU (lsuc (l1 ⊔ l2))
  type-impredicative-exists-Prop =
    type-Prop impredicative-exists-Prop

  map-impredicative-exists-Prop :
    exists A P → type-impredicative-exists-Prop
  map-impredicative-exists-Prop =
    map-universal-property-trunc-Prop
      ( impredicative-exists-Prop)
      ( ind-Σ (λ x y Q h → h x y))

  map-inv-impredicative-exists-Prop :
    type-impredicative-exists-Prop → exists A P
  map-inv-impredicative-exists-Prop H =
    H (∃ A P) (λ x y → unit-trunc-Prop (x , y))

  equiv-impredicative-exists-Prop :
    exists A P ≃ type-impredicative-exists-Prop
  equiv-impredicative-exists-Prop =
    equiv-iff
      ( ∃ A P)
      ( impredicative-exists-Prop)
      ( map-impredicative-exists-Prop)
      ( map-inv-impredicative-exists-Prop)
```

### The impredicative encoding of the based identity type of a set

```agda
module _
  {l : Level} (A : Set l) (a x : type-Set A)
  where

  impredicative-based-id-Prop : Prop (lsuc l)
  impredicative-based-id-Prop = ∀' (type-Set A → Prop l) (λ Q → Q a ⇒ Q x)

  type-impredicative-based-id-Prop : UU (lsuc l)
  type-impredicative-based-id-Prop = type-Prop impredicative-based-id-Prop

  map-impredicative-based-id-Prop :
    a ＝ x → type-impredicative-based-id-Prop
  map-impredicative-based-id-Prop refl Q p = p

  map-inv-impredicative-based-id-Prop :
    type-impredicative-based-id-Prop → a ＝ x
  map-inv-impredicative-based-id-Prop H = H (Id-Prop A a) refl

  equiv-impredicative-based-id-Prop :
    (a ＝ x) ≃ type-impredicative-based-id-Prop
  equiv-impredicative-based-id-Prop =
    equiv-iff
      ( Id-Prop A a x)
      ( impredicative-based-id-Prop)
      ( map-impredicative-based-id-Prop)
      ( map-inv-impredicative-based-id-Prop)
```

### The impredicative encoding of Martin-Löf's identity type of a set

```agda
module _
  {l : Level} (A : Set l) (x y : type-Set A)
  where

  impredicative-id-Prop : Prop (lsuc l)
  impredicative-id-Prop =
    ∀'
      ( type-Set A → type-Set A → Prop l)
      ( λ Q → (∀' (type-Set A) (λ a → Q a a)) ⇒ Q x y)

  type-impredicative-id-Prop : UU (lsuc l)
  type-impredicative-id-Prop = type-Prop impredicative-id-Prop

  map-impredicative-id-Prop :
    x ＝ y → type-impredicative-id-Prop
  map-impredicative-id-Prop refl Q r = r x

  map-inv-impredicative-id-Prop :
    type-impredicative-id-Prop → x ＝ y
  map-inv-impredicative-id-Prop H = H (Id-Prop A) (refl-htpy)

  equiv-impredicative-id-Prop :
    (x ＝ y) ≃ type-impredicative-id-Prop
  equiv-impredicative-id-Prop =
    equiv-iff
      ( Id-Prop A x y)
      ( impredicative-id-Prop)
      ( map-impredicative-id-Prop)
      ( map-inv-impredicative-id-Prop)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [Constructing coproduct types and boolean types from universes](https://mathoverflow.net/questions/457904/constructing-coproduct-types-and-boolean-types-from-universes)
  at mathoverflow
