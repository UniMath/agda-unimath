# Extension of finite sequences at an index

```agda
module lists.extend-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`,
the [functor](lists.functoriality-finite-sequences.md) of
[finite sequences](lists.finite-sequences.md) of length `n+1`,
`A ↦ Ｖₙ₊₁(A) = Aⁿ⁺¹` has `n+1` co-unit maps given by

```text
  εᵢ : (x₀,...xᵢ₋₁,xᵢ,xᵢ₊₁,...,xₙ) ↦ xᵢ
```

The
{{#concept "duplication map" Disambiguation="of finite sequences at an index Agda=dupl-at-fin-sequence}}
at [index](univalent-combinatorics.standard-finite-types.md) `i` is the map
`δᵢ : Ｖₙ₊₁(A) → Ｍₙ₊₁(A) = (Aⁿ⁺¹)ⁿ⁺¹` given by

```text
  δᵢ : x ↦  (mⱼ,ₖ) = (xⱼ₊ₖ₋ᵢ)
```

where the index `j+k-i` is taken
[modulo `n+1`](elementary-number-theory.modular-arithmetic.md).

The pair `(εᵢ , δᵢ)` is natural: any map `f : A → B` induces a commutative
diagram:

```text
         εᵢ              δᵢ
    A <------ Ｖₙ₊₁(A) ------> Ｍₙ₊₁(A)
    |            |               |
    |            |               |
  f |            |               |
    |            |               |
    |            |               |
    v            v               v
    B <------ Ｖₙ₊₁(B) ------> Ｍₙ₊₁(B)
```

and satisfy the [comonad laws](category-theory.comonads-on-precategories.md):

- `(Ｖₙ₊₁ • δᵢ) ∘ δᵢ ~ (δᵢ • Ｖₙ₊₁) ∘ δᵢ`;
- `(Ｖₙ₊₁ • εᵢ) ∘ δᵢ ~ id`;
- `(εᵢ • Ｖₙ₊₁) ∘ δᵢ ~ id`;

The
{{#concept "extension map" Disambiguation="of a finite sequences at an index" Agda=extend-at-fin-sequence}}
at the index `i` is the corresponding co-Kleisli extension:

```text
  extᵢ : (Ｖₙ₊₁(A) → B) → Ｖₙ₊₁(A) → Ｖₙ₊₁(B)
  extᵢ f = (Ｖₙ₊₁ • f) ∘ δᵢ
```

## Definitions

### The duplication map at and index

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  dupl-at-fin-sequence :
    fin-sequence A (succ-ℕ n) →
    fin-sequence (fin-sequence A (succ-ℕ n)) (succ-ℕ n)
  dupl-at-fin-sequence u j k =
    elem-at-fin-sequence
      ( succ-ℕ n)
      ( add-ℤ-Mod
        ( succ-ℕ n)
        ( add-ℤ-Mod (succ-ℕ n) j k)
        ( neg-ℤ-Mod (succ-ℕ n) i))
      ( u)
```

### Extension map at an index

```agda
module _
  {l l' : Level} {A : UU l} {B : UU l'} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  extend-at-fin-sequence :
    (fin-sequence A (succ-ℕ n) → B) →
    fin-sequence A (succ-ℕ n) →
    fin-sequence B (succ-ℕ n)
  extend-at-fin-sequence f =
    map-fin-sequence (succ-ℕ n) f ∘ dupl-at-fin-sequence n i
```

## Properties

### Associativity law

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  compute-map-dupl-at-fin-sequence :
    (u : fin-sequence A (succ-ℕ n)) →
    map-fin-sequence
      ( succ-ℕ n)
      ( dupl-at-fin-sequence n i)
      ( dupl-at-fin-sequence n i u) ~
    dupl-at-fin-sequence n i
      ( dupl-at-fin-sequence n i u)
  compute-map-dupl-at-fin-sequence u j =
    eq-htpy
      ( λ k →
        eq-htpy
          ( λ p →
            ap
              ( u ∘ add-ℤ-Mod' (succ-ℕ n) (neg-ℤ-Mod (succ-ℕ n) i))
              ( lemma k p (neg-ℤ-Mod (succ-ℕ n) i))))
    where

    lemma :
      (k p q : Fin (succ-ℕ n)) →
      add-ℤ-Mod
        ( succ-ℕ n)
        ( j)
        ( add-ℤ-Mod
          ( succ-ℕ n)
          ( add-ℤ-Mod (succ-ℕ n) k p)
          ( q)) ＝
      add-ℤ-Mod
        ( succ-ℕ n)
        ( add-ℤ-Mod
          ( succ-ℕ n)
          ( add-ℤ-Mod (succ-ℕ n) j k)
          ( q))
        ( p)
    lemma k p q =
      ( inv
        ( associative-add-ℤ-Mod
          ( succ-ℕ n)
          ( j)
          ( add-ℤ-Mod (succ-ℕ n) k p)
          ( q))) ∙
      ( ap
        ( add-ℤ-Mod' (succ-ℕ n) q)
        ( inv (associative-add-ℤ-Mod (succ-ℕ n) j k p))) ∙
      ( associative-add-ℤ-Mod
        ( succ-ℕ n)
        ( add-ℤ-Mod (succ-ℕ n) j k)
        ( p)
        ( q)) ∙
      ( ap
        ( add-ℤ-Mod (succ-ℕ n) (add-ℤ-Mod (succ-ℕ n) j k))
        ( commutative-add-ℤ-Mod (succ-ℕ n) p q)) ∙
      ( inv
        ( associative-add-ℤ-Mod
          ( succ-ℕ n)
          ( add-ℤ-Mod (succ-ℕ n) j k)
          ( q)
          ( p)))
```

### Unit laws

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  compute-map-elem-at-dupl-at-fin-sequence :
    (u : fin-sequence A (succ-ℕ n)) →
    map-fin-sequence
      ( succ-ℕ n)
      ( elem-at-fin-sequence (succ-ℕ n) i)
      ( dupl-at-fin-sequence n i u) ~
    u
  compute-map-elem-at-dupl-at-fin-sequence u k =
    ap u
      ( ( associative-add-ℤ-Mod (succ-ℕ n) k i (neg-ℤ-Mod (succ-ℕ n) i)) ∙
        ( ap
          ( add-ℤ-Mod (succ-ℕ n) k)
          ( right-inverse-law-add-ℤ-Mod (succ-ℕ n) i)) ∙
        ( right-unit-law-add-ℤ-Mod (succ-ℕ n) k))

  compute-elem-at-dupl-at-fin-sequence :
    (u : fin-sequence A (succ-ℕ n)) →
    elem-at-fin-sequence (succ-ℕ n) i
      ( dupl-at-fin-sequence n i u) ~
    u
  compute-elem-at-dupl-at-fin-sequence u k =
    ap u
      ( ( ap
          ( add-ℤ-Mod' (succ-ℕ n) (neg-ℤ-Mod (succ-ℕ n) i))
          ( commutative-add-ℤ-Mod (succ-ℕ n) i k)) ∙
        ( associative-add-ℤ-Mod (succ-ℕ n) k i (neg-ℤ-Mod (succ-ℕ n) i)) ∙
        ( ap
          ( add-ℤ-Mod (succ-ℕ n) k)
          ( right-inverse-law-add-ℤ-Mod (succ-ℕ n) i)) ∙
        ( right-unit-law-add-ℤ-Mod (succ-ℕ n) k))
```

### Extending the co-unit is the identity

```agda
module _
  {l : Level} {A : UU l} (n : ℕ) (i : Fin (succ-ℕ n))
  where

  compute-extend-at-elem-at-fin-sequence :
    (u : fin-sequence A (succ-ℕ n)) →
    extend-at-fin-sequence
      ( n)
      ( i)
      ( elem-at-fin-sequence (succ-ℕ n) i)
      ( u) ~
    u
  compute-extend-at-elem-at-fin-sequence =
    compute-map-elem-at-dupl-at-fin-sequence n i
```
