# Trivial Σ-Decompositions

```agda
module foundation.trivial-sigma-decompositions where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

## Definitions

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  trivial-Σ-Decomposition-inhabited :
    (p : is-inhabited A) → Σ-Decomposition lzero l1 A
  pr1 (trivial-Σ-Decomposition-inhabited p) = unit
  pr1 (pr2 (trivial-Σ-Decomposition-inhabited p))  = λ _ → (A , p)
  pr2 (pr2 (trivial-Σ-Decomposition-inhabited p)) =
    inv-left-unit-law-Σ-is-contr
      ( is-contr-unit)
      ( star)

  trivial-Σ-Decomposition-empty :
    (p : is-empty A) → Σ-Decomposition lzero lzero A
  pr1 (trivial-Σ-Decomposition-empty p) = empty
  pr1 (pr2 (trivial-Σ-Decomposition-empty p)) = ex-falso
  pr2 (pr2 (trivial-Σ-Decomposition-empty p)) =
    equiv-is-empty
      ( p)
      ( map-left-absorption-Σ _)

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-trivial-Σ-Decomposition :
    UU l2
  is-trivial-Σ-Decomposition = is-contr (indexing-type-Σ-Decomposition D)
```

## Propositions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  ( is-trivial : is-trivial-Σ-Decomposition D)
  where

  is-inhabited-base-type-is-trivial-Σ-Decomposition :
    is-inhabited A
  is-inhabited-base-type-is-trivial-Σ-Decomposition =
    map-equiv-trunc-Prop
      ( inv-equiv (matching-correspondence-Σ-Decomposition D) ∘e
        inv-left-unit-law-Σ-is-contr is-trivial ( center is-trivial))
      ( is-inhabited-cotype-Σ-Decomposition D ( center is-trivial))

  equiv-trivial-is-trivial-Σ-Decomposition :
    equiv-Σ-Decomposition D
      ( trivial-Σ-Decomposition-inhabited
        ( A)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition ))
  pr1 equiv-trivial-is-trivial-Σ-Decomposition =
    ( terminal-map , ( is-equiv-terminal-map-is-contr is-trivial))
  pr1 (pr2 equiv-trivial-is-trivial-Σ-Decomposition) =
    ( λ x →
      ( ( inv-equiv (matching-correspondence-Σ-Decomposition D)) ∘e
        ( inv-left-unit-law-Σ-is-contr is-trivial x )))
  pr2 (pr2 equiv-trivial-is-trivial-Σ-Decomposition ) a =
    eq-pair-Σ
      ( refl)
      ( inv-map-eq-transpose-equiv
        ( inv-equiv (matching-correspondence-Σ-Decomposition D))
        ( refl))
```
