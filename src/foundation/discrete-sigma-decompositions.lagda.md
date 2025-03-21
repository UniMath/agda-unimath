# Discrete Σ-decompositions

```agda
module foundation.discrete-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.raising-universe-levels-unit-type
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Definition

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  discrete-Σ-Decomposition :
    Σ-Decomposition l1 l2 A
  pr1 discrete-Σ-Decomposition = A
  pr1 (pr2 discrete-Σ-Decomposition) a =
    ( raise-unit l2 , unit-trunc-Prop (raise-star))
  pr2 (pr2 discrete-Σ-Decomposition) =
    inv-equiv
      ( equiv-pr1
        ( λ _ →
          is-contr-raise-unit))

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-discrete-Prop-Σ-Decomposition : Prop (l2 ⊔ l3)
  is-discrete-Prop-Σ-Decomposition =
    Π-Prop
      ( indexing-type-Σ-Decomposition D)
      ( λ x → is-contr-Prop (cotype-Σ-Decomposition D x))

  is-discrete-Σ-Decomposition :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition =
    type-Prop (is-discrete-Prop-Σ-Decomposition)

is-discrete-discrete-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-discrete-Σ-Decomposition (discrete-Σ-Decomposition l2 A)
is-discrete-discrete-Σ-Decomposition = λ x → is-contr-raise-unit

type-discrete-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Σ-Decomposition {l1} {l2} {l3} {A} =
  type-subtype (is-discrete-Prop-Σ-Decomposition {l1} {l2} {l3} {A})
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  (is-discrete : is-discrete-Σ-Decomposition D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition :
    equiv-Σ-Decomposition D (discrete-Σ-Decomposition l4 A)
  pr1 equiv-discrete-is-discrete-Σ-Decomposition =
    ( inv-equiv
      ( right-unit-law-Σ-is-contr is-discrete ∘e
        matching-correspondence-Σ-Decomposition D))
  pr1 (pr2 equiv-discrete-is-discrete-Σ-Decomposition) x =
    equiv-raise-unit-is-contr (is-discrete x)
  pr2 (pr2 equiv-discrete-is-discrete-Σ-Decomposition) a =
    eq-pair-Σ
      ( ap ( λ f → map-equiv f a)
        ( ( left-inverse-law-equiv
            ( equiv-pr1 is-discrete ∘e
              matching-correspondence-Σ-Decomposition D)) ∙
        ( ( inv
            ( right-inverse-law-equiv
              ( equiv-pr1 ( λ _ → is-contr-raise-unit)))))))
      ( eq-is-contr is-contr-raise-unit)

is-contr-type-discrete-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr (type-discrete-Σ-Decomposition {l1} {l1} {l2} {A})
pr1 ( is-contr-type-discrete-Σ-Decomposition {l1} {l2} {A}) =
  ( discrete-Σ-Decomposition l2 A , is-discrete-discrete-Σ-Decomposition)
pr2 ( is-contr-type-discrete-Σ-Decomposition {l1} {l2} {A}) =
  ( λ x →
    eq-type-subtype
      ( is-discrete-Prop-Σ-Decomposition)
      ( inv
        ( eq-equiv-Σ-Decomposition
          ( pr1 x)
          ( discrete-Σ-Decomposition l2 A)
          ( equiv-discrete-is-discrete-Σ-Decomposition (pr1 x) (pr2 x)))))
```
