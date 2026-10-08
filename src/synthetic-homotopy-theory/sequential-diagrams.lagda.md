# Sequential diagrams

```agda
module synthetic-homotopy-theory.sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.universe-levels
```

</details>

## Idea

A **sequential diagram** `(A, a)` is a [sequence](lists.sequences.md) of types
`A : ℕ → 𝒰` over the natural numbers, equipped with a family of maps
`aₙ : Aₙ → Aₙ₊₁` for all `n`.

They can be represented by diagrams

```text
     a₀      a₁      a₂
 A₀ ---> A₁ ---> A₂ ---> ⋯
```

extending infinitely to the right.

Sequential diagrams are dual to
[inverse sequential diagrams](foundation.inverse-sequential-diagrams.md), and
are also sometimes called **cotowers**.

## Definition

```agda
sequential-diagram : (l : Level) → UU (lsuc l)
sequential-diagram l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A n → A (succ-ℕ n))

module _
  { l : Level} (A : sequential-diagram l)
  where

  family-sequential-diagram : ℕ → UU l
  family-sequential-diagram = pr1 A

  map-sequential-diagram :
    (n : ℕ) → family-sequential-diagram n → family-sequential-diagram (succ-ℕ n)
  map-sequential-diagram = pr2 A
```

```agda
module _
  { l : Level} (X : UU l)
  where

  constant-sequential-diagram : sequential-diagram l
  pr1 constant-sequential-diagram _ = X
  pr2 constant-sequential-diagram _ x = x
```

## Properties

The [identity type](foundation.identity-types.md) of sequential diagrams is
characterized in the file about
[equivalences of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md).

### Postcomposition sequential diagrams

Given a sequential diagram `A` and a type `X` there is a sequential diagram
`X → A` defined by levelwise postcomposition.

```text
           (f₀ ∘ -)          (f₁ ∘ -)          (f₂ ∘ -)
  (X → A₀) -------> (X → A₁) -------> (X → A₂) -------> (X → A₃) -------> ⋯
```

```agda
module _
  {l1 l2 : Level} (X : UU l1) (A : sequential-diagram l2)
  where

  postcomp-sequential-diagram : sequential-diagram (l1 ⊔ l2)
  pr1 postcomp-sequential-diagram n = X → family-sequential-diagram A n
  pr2 postcomp-sequential-diagram n g x = map-sequential-diagram A n (g x)
```

### A sequential diagram of contractible types consists of equivalences

This is an easy corollary of the fact that every map between
[contractible types](foundation-core.contractible-types.md) is an
[equivalence](foundation-core.equivalences.md).

```agda
module _
  {l1 : Level} {A : sequential-diagram l1}
  where

  is-equiv-sequential-diagram-is-contr :
    ((n : ℕ) → is-contr (family-sequential-diagram A n)) →
    (n : ℕ) → is-equiv (map-sequential-diagram A n)
  is-equiv-sequential-diagram-is-contr contrs n =
    is-equiv-is-contr
      ( map-sequential-diagram A n)
      ( contrs n)
      ( contrs (succ-ℕ n))
```

## References

{{#bibliography}} {{#reference SvDR20}}
