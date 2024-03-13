# Impredicative encodings of the logical operations

```agda
module foundation.impredicative-encodings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.homotopies
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universal-quantification
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
impredicative-trunc-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-trunc-Prop {l} A =
  Π-Prop
    ( Prop l)
    ( λ Q → function-Prop (A → type-Prop Q) Q)

type-impredicative-trunc-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-trunc-Prop A =
  type-Prop (impredicative-trunc-Prop A)

map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A → type-impredicative-trunc-Prop A
map-impredicative-trunc-Prop A =
  map-universal-property-trunc-Prop
    ( impredicative-trunc-Prop A)
    ( λ x Q f → f x)

map-inv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-trunc-Prop A → type-trunc-Prop A
map-inv-impredicative-trunc-Prop A H =
  H (trunc-Prop A) unit-trunc-Prop

equiv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A ≃ type-impredicative-trunc-Prop A
equiv-impredicative-trunc-Prop A =
  equiv-iff
    ( trunc-Prop A)
    ( impredicative-trunc-Prop A)
    ( map-impredicative-trunc-Prop A)
    ( map-inv-impredicative-trunc-Prop A)
```

### The impredicative encoding of conjunction

```agda
impredicative-conjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-conjunction-Prop {l1} {l2} P1 P2 =
  ∀' (Prop (l1 ⊔ l2)) (λ Q → (P1 →₍₋₁₎ (P2 →₍₋₁₎ Q)) →₍₋₁₎ Q)

type-impredicative-conjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-conjunction-Prop P1 P2 =
  type-Prop (impredicative-conjunction-Prop P1 P2)

map-product-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-product-Prop P1 P2 → type-impredicative-conjunction-Prop P1 P2
map-product-impredicative-conjunction-Prop P1 P2 (p1 , p2) Q f = f p1 p2

map-inv-product-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-conjunction-Prop P1 P2 → type-product-Prop P1 P2
map-inv-product-impredicative-conjunction-Prop P1 P2 H = H (P1 ∧₍₋₁₎ P2) pair

equiv-product-impredicative-conjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-product-Prop P1 P2 ≃ type-impredicative-conjunction-Prop P1 P2
equiv-product-impredicative-conjunction-Prop P1 P2 =
  equiv-iff
    ( P1 ∧₍₋₁₎ P2)
    ( impredicative-conjunction-Prop P1 P2)
    ( map-product-impredicative-conjunction-Prop P1 P2)
    ( map-inv-product-impredicative-conjunction-Prop P1 P2)
```

### The impredicative encoding of disjunction

```agda
impredicative-disjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (lsuc (l1 ⊔ l2))
impredicative-disjunction-Prop {l1} {l2} P1 P2 =
  ∀' (Prop (l1 ⊔ l2)) (λ Q → (P1 →₍₋₁₎ Q) →₍₋₁₎ ((P2 →₍₋₁₎ Q) →₍₋₁₎ Q))

type-impredicative-disjunction-Prop :
  {l1 l2 : Level} → Prop l1 → Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-disjunction-Prop P1 P2 =
  type-Prop (impredicative-disjunction-Prop P1 P2)

map-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disjunction-Prop P1 P2 → type-impredicative-disjunction-Prop P1 P2
map-impredicative-disjunction-Prop P1 P2 =
  map-universal-property-trunc-Prop
    ( impredicative-disjunction-Prop P1 P2)
    ( rec-coproduct
      ( λ x Q f1 f2 → f1 x)
      ( λ y Q f1 f2 → f2 y))

map-inv-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-impredicative-disjunction-Prop P1 P2 → type-disjunction-Prop P1 P2
map-inv-impredicative-disjunction-Prop P1 P2 H =
  H (P1 ∨₍₋₁₎ P2) (inl-disjunction) (inr-disjunction)

equiv-impredicative-disjunction-Prop :
  {l1 l2 : Level} (P1 : Prop l1) (P2 : Prop l2) →
  type-disjunction-Prop P1 P2 ≃ type-impredicative-disjunction-Prop P1 P2
equiv-impredicative-disjunction-Prop P1 P2 =
  equiv-iff
    ( P1 ∨₍₋₁₎ P2)
    ( impredicative-disjunction-Prop P1 P2)
    ( map-impredicative-disjunction-Prop P1 P2)
    ( map-inv-impredicative-disjunction-Prop P1 P2)
```

### The impredicative encoding of the empty type

```agda
impredicative-empty-Prop : (l : Level) → Prop (lsuc l)
impredicative-empty-Prop l = ∀' (Prop l) (λ P → P)

type-impredicative-empty-Prop : (l : Level) → UU (lsuc l)
type-impredicative-empty-Prop l = type-Prop (impredicative-empty-Prop l)

is-empty-impredicative-empty-Prop :
  {l : Level} → is-empty (type-impredicative-empty-Prop l)
is-empty-impredicative-empty-Prop {l} e =
  is-empty-raise-empty (e (raise-empty-Prop l))

equiv-impredicative-empty-Prop :
  {l : Level} → empty ≃ type-impredicative-empty-Prop l
equiv-impredicative-empty-Prop =
  equiv-is-empty id is-empty-impredicative-empty-Prop
```

### The impredicative encoding of negation

```agda
impredicative-neg-Prop :
  {l : Level} → UU l → Prop (lsuc l)
impredicative-neg-Prop {l} A =
  Π-Prop (Prop l) (λ Q → function-Prop A Q)

type-impredicative-neg-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-neg-Prop A =
  type-Prop (impredicative-neg-Prop A)

map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A → type-impredicative-neg-Prop A
map-impredicative-neg-Prop A f Q a = ex-falso (f a)

map-inv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-neg-Prop A → ¬ A
map-inv-impredicative-neg-Prop A H a = H (neg-prop-Type A) a a

equiv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A ≃ type-impredicative-neg-Prop A
equiv-impredicative-neg-Prop A =
  equiv-iff
    ( neg-prop-Type A)
    ( impredicative-neg-Prop A)
    ( map-impredicative-neg-Prop A)
    ( map-inv-impredicative-neg-Prop A)
```

### The impredicative encoding of existential quantification

```agda
impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → Prop (lsuc (l1 ⊔ l2))
impredicative-exists-Prop {l1} {l2} {A} P =
  ∀'
    ( Prop (l1 ⊔ l2))
    ( λ Q → (∀' A (λ x → (P x) →₍₋₁₎ Q)) →₍₋₁₎ Q)

type-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) → UU (lsuc (l1 ⊔ l2))
type-impredicative-exists-Prop P =
  type-Prop (impredicative-exists-Prop P)

map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P → type-impredicative-exists-Prop P
map-impredicative-exists-Prop P =
  map-universal-property-trunc-Prop
    ( impredicative-exists-Prop P)
    ( ind-Σ (λ x y Q h → h x y))

map-inv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  type-impredicative-exists-Prop P → exists A P
map-inv-impredicative-exists-Prop {A = A} P H =
  H (exists-Prop A P) (λ x y → unit-trunc-Prop (x , y))

equiv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → Prop l2) →
  exists A P ≃ type-impredicative-exists-Prop P
equiv-impredicative-exists-Prop {A = A} P =
  equiv-iff
    ( exists-Prop A P)
    ( impredicative-exists-Prop P)
    ( map-impredicative-exists-Prop P)
    ( map-inv-impredicative-exists-Prop P)
```

### The impredicative encoding of the based identity type of a set

```agda
impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → Prop (lsuc l)
impredicative-based-id-Prop {l} A a x =
  ∀' (type-Set A → Prop l) (λ Q → (Q a) →₍₋₁₎ (Q x))

type-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) → UU (lsuc l)
type-impredicative-based-id-Prop A a x =
  type-Prop (impredicative-based-id-Prop A a x)

map-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  a ＝ x → type-impredicative-based-id-Prop A a x
map-impredicative-based-id-Prop A a .a refl Q p = p

map-inv-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  type-impredicative-based-id-Prop A a x → a ＝ x
map-inv-impredicative-based-id-Prop A a x H =
  H (Id-Prop A a) refl

equiv-impredicative-based-id-Prop :
  {l : Level} (A : Set l) (a x : type-Set A) →
  (a ＝ x) ≃ type-impredicative-based-id-Prop A a x
equiv-impredicative-based-id-Prop A a x =
  equiv-iff
    ( Id-Prop A a x)
    ( impredicative-based-id-Prop A a x)
    ( map-impredicative-based-id-Prop A a x)
    ( map-inv-impredicative-based-id-Prop A a x)
```

### The impredicative encoding of Martin-Löf's identity type of a set

```agda
impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → Prop (lsuc l)
impredicative-id-Prop {l} A x y =
  ∀'
    ( type-Set A → type-Set A → Prop l)
    ( λ Q → (∀' (type-Set A) (λ a → Q a a)) →₍₋₁₎ (Q x y))

type-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) → UU (lsuc l)
type-impredicative-id-Prop A x y =
  type-Prop (impredicative-id-Prop A x y)

map-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  x ＝ y → type-impredicative-id-Prop A x y
map-impredicative-id-Prop A x .x refl Q r = r x

map-inv-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  type-impredicative-id-Prop A x y → x ＝ y
map-inv-impredicative-id-Prop A x y H =
  H (Id-Prop A) (refl-htpy)

equiv-impredicative-id-Prop :
  {l : Level} (A : Set l) (x y : type-Set A) →
  (x ＝ y) ≃ type-impredicative-id-Prop A x y
equiv-impredicative-id-Prop A x y =
  equiv-iff
    ( Id-Prop A x y)
    ( impredicative-id-Prop A x y)
    ( map-impredicative-id-Prop A x y)
    ( map-inv-impredicative-id-Prop A x y)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External

- [Constructing coproduct types and boolean types from universes](https://mathoverflow.net/questions/457904/constructing-coproduct-types-and-boolean-types-from-universes)
  at mathoverflow
