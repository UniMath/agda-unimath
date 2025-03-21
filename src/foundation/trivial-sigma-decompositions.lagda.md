# Trivial Σ-decompositions

```agda
module foundation.trivial-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.raising-universe-levels-unit-type
open import foundation.sigma-decompositions
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  trivial-inhabited-Σ-Decomposition :
    (p : is-inhabited A) → Σ-Decomposition l2 l1 A
  pr1 (trivial-inhabited-Σ-Decomposition p) = raise-unit l2
  pr1 (pr2 (trivial-inhabited-Σ-Decomposition p)) = λ _ → (A , p)
  pr2 (pr2 (trivial-inhabited-Σ-Decomposition p)) =
    inv-left-unit-law-Σ-is-contr
      ( is-contr-raise-unit)
      ( raise-star)

  trivial-empty-Σ-Decomposition :
    (p : is-empty A) → Σ-Decomposition lzero lzero A
  pr1 (trivial-empty-Σ-Decomposition p) = empty
  pr1 (pr2 (trivial-empty-Σ-Decomposition p)) = ex-falso
  pr2 (pr2 (trivial-empty-Σ-Decomposition p)) =
    equiv-is-empty
      ( p)
      ( map-left-absorption-Σ _)

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-trivial-Prop-Σ-Decomposition : Prop l2
  is-trivial-Prop-Σ-Decomposition =
    is-contr-Prop (indexing-type-Σ-Decomposition D)

  is-trivial-Σ-Decomposition : UU l2
  is-trivial-Σ-Decomposition = type-Prop is-trivial-Prop-Σ-Decomposition

is-trivial-trivial-inhabited-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} (p : is-inhabited A) →
  is-trivial-Σ-Decomposition (trivial-inhabited-Σ-Decomposition l2 A p)
is-trivial-trivial-inhabited-Σ-Decomposition p = is-contr-raise-unit

type-trivial-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-trivial-Σ-Decomposition {l1} {l2} {l3} {A} =
  type-subtype (is-trivial-Prop-Σ-Decomposition {l1} {l2} {l3} {A})
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
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
      ( trivial-inhabited-Σ-Decomposition
        ( l4)
        ( A)
        ( is-inhabited-base-type-is-trivial-Σ-Decomposition))
  pr1 equiv-trivial-is-trivial-Σ-Decomposition =
    equiv-raise-unit-is-contr is-trivial
  pr1 (pr2 equiv-trivial-is-trivial-Σ-Decomposition) =
    ( λ x →
      ( ( inv-equiv (matching-correspondence-Σ-Decomposition D)) ∘e
        ( inv-left-unit-law-Σ-is-contr is-trivial x)))
  pr2 (pr2 equiv-trivial-is-trivial-Σ-Decomposition) a =
    eq-pair-eq-fiber
      ( map-inv-eq-transpose-equiv
        ( inv-equiv (matching-correspondence-Σ-Decomposition D))
        ( refl))

is-contr-type-trivial-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  (p : is-inhabited A) →
  is-contr (type-trivial-Σ-Decomposition {l1} {l2} {l1} {A})
pr1 ( is-contr-type-trivial-Σ-Decomposition {l1} {l2} {A} p) =
  ( trivial-inhabited-Σ-Decomposition l2 A p ,
    is-trivial-trivial-inhabited-Σ-Decomposition p)
pr2 ( is-contr-type-trivial-Σ-Decomposition {l1} {l2} {A} p) x =
  eq-type-subtype
    ( is-trivial-Prop-Σ-Decomposition)
    ( inv
      ( eq-equiv-Σ-Decomposition
        ( pr1 x)
        ( trivial-inhabited-Σ-Decomposition l2 A p)
        ( equiv-trivial-is-trivial-Σ-Decomposition (pr1 x) (pr2 x))))
```
