# Iterated cartesian product types

```agda
module foundation.iterated-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In these file, we give three definitions of the iterated cartesian product
`A₁ × ... × Aₙ` of `n` types `A₁ , ... , Aₙ`. Two uses a family of types over
`Fin n`: the first use recursion over `Fin n` and the second is just
`Π (Fin n) A`. The last one use lists. We also show that the first two
definitions are equivalent.

## Definitions

### Via a family of types over `Fin n`

#### Using recursion

```agda
iterated-product-Fin-recursive :
  {l : Level} (n : ℕ) →
  ((Fin n) → UU l) → UU l
iterated-product-Fin-recursive {l} zero-ℕ A = raise-unit l
iterated-product-Fin-recursive (succ-ℕ n) A =
  A (inr star) × iterated-product-Fin-recursive n (A ∘ inl)
```

#### Using `Π` type

```agda
iterated-product-Fin-Π :
  {l : Level} (n : ℕ) →
  ((Fin n) → UU l) → UU l
iterated-product-Fin-Π n A = (i : Fin n) → A i
```

### Via lists

```agda
iterated-product-lists :
  {l : Level} → list (UU l) → UU l
iterated-product-lists {l} nil = raise-unit l
iterated-product-lists (cons A p) = A × iterated-product-lists p
```

## Property

### Equivalence between the first two definitions

```agda
equiv-iterated-product-Fin-recursive-Π :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) →
  iterated-product-Fin-recursive n A ≃
  iterated-product-Fin-Π n A
equiv-iterated-product-Fin-recursive-Π zero-ℕ A =
  equiv-is-contr is-contr-raise-unit (dependent-universal-property-empty' A)
equiv-iterated-product-Fin-recursive-Π (succ-ℕ n) A =
  ( ( inv-equiv (equiv-dependent-universal-property-coprod A)) ∘e
    ( ( commutative-prod) ∘e
      ( ( equiv-prod
            ( inv-equiv (left-unit-law-Π-is-contr is-contr-unit star))
            ( id-equiv)) ∘e
        ( ( equiv-prod
              ( id-equiv)
              ( equiv-iterated-product-Fin-recursive-Π n (A ∘ inl)))))))
```
