# Equivalences of towers of types

```agda
module foundation.equivalences-towers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.towers
open import foundation.universe-levels
open import foundation.equivalences
open import foundation.maps-towers
open import foundation.identity-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.identity-types
open import foundation.contractible-types
open import foundation.structure-identity-principle
open import foundation.equality-dependent-function-types
open import foundation.univalence
open import foundation.homotopy-induction
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels
open import foundation.equivalences

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

An **equivalence of towers** `A ≃ B` is a commuting diagram of the form

```text
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀
  |        |         |       |       |        |
  ⋯        |         |       ⋯       |        |
  v        v         v       v       v        v
  ⋯ ----> Bₙ₊₁ ----> Bₙ ----> ⋯ ----> B₁ ----> B₀.
```

where every vertical map is an [equivalence](foundation-core.equivalences.md).

## Definitions

```agda
equiv-Tower :
  {l1 l2 : Level} (A : Tower l1) (B : Tower l2) → UU (l1 ⊔ l2)
equiv-Tower A B =
  Σ ( (n : ℕ) → type-Tower A n ≃ type-Tower B n)
    ( λ e → (n : ℕ) → naturality-hom-Tower A B (map-equiv ∘ e) n)

hom-equiv-Tower :
  {l1 l2 : Level} (A : Tower l1) (B : Tower l2) →
  equiv-Tower A B → hom-Tower A B
pr1 (hom-equiv-Tower A B e) n = pr1 (pr1 e n)
pr2 (hom-equiv-Tower A B e) = pr2 e
```

## Properties

### Characterizing equality of towers

```agda
refl-equiv-Tower :
  {l : Level} (A : Tower l) → equiv-Tower A A
pr1 (refl-equiv-Tower A) n = id-equiv
pr2 (refl-equiv-Tower A) n = refl-htpy

equiv-eq-Tower :
  {l : Level} (A B : Tower l) → A ＝ B → equiv-Tower A B
equiv-eq-Tower A .A refl = refl-equiv-Tower A

is-contr-total-equiv-Tower :
  {l : Level} (A : Tower l) →
  is-contr (Σ (Tower l) (equiv-Tower A))
is-contr-total-equiv-Tower A =
  is-contr-total-Eq-structure _
    ( is-contr-total-Eq-Π
      ( λ n → type-Tower A n ≃_)
      ( λ n → is-contr-total-equiv (type-Tower A n)))
    ( type-Tower A , λ n → id-equiv)
    ( is-contr-total-Eq-Π _
      ( λ n → is-contr-total-htpy (map-Tower A n)))

is-equiv-equiv-eq-Tower :
  {l : Level} (A B : Tower l) → is-equiv (equiv-eq-Tower A B)
is-equiv-equiv-eq-Tower A =
  fundamental-theorem-id
    ( is-contr-total-equiv-Tower A)
    ( equiv-eq-Tower A)

eq-equiv-Tower :
  {l : Level} {A B : Tower l} → equiv-Tower A B → A ＝ B
eq-equiv-Tower {A = A} {B} = map-inv-is-equiv (is-equiv-equiv-eq-Tower A B)
```
