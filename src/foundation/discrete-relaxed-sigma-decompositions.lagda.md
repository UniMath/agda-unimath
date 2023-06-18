# Discrete relaxed Σ-decompositions

```agda
module foundation.discrete-relaxed-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.relaxed-sigma-decompositions
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

  discrete-Relaxed-Σ-Decomposition :
    Relaxed-Σ-Decomposition l1 l2 A
  pr1 discrete-Relaxed-Σ-Decomposition = A
  pr1 (pr2 discrete-Relaxed-Σ-Decomposition) a = raise-unit l2
  pr2 (pr2 discrete-Relaxed-Σ-Decomposition) =
    inv-equiv
      ( equiv-pr1
        ( λ _ →
          is-contr-raise-unit))

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  where

  is-discrete-Prop-Relaxed-Σ-Decomposition : Prop (l2 ⊔ l3)
  is-discrete-Prop-Relaxed-Σ-Decomposition =
    Π-Prop
      ( indexing-type-Relaxed-Σ-Decomposition D)
      ( λ x → is-contr-Prop (cotype-Relaxed-Σ-Decomposition D x))

  is-discrete-Relaxed-Σ-Decomposition :
    UU (l2 ⊔ l3)
  is-discrete-Relaxed-Σ-Decomposition =
    type-Prop (is-discrete-Prop-Relaxed-Σ-Decomposition)

is-discrete-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-discrete-Relaxed-Σ-Decomposition (discrete-Relaxed-Σ-Decomposition l2 A)
is-discrete-discrete-Relaxed-Σ-Decomposition = λ x → is-contr-raise-unit

type-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 l3 : Level} {A : UU l1} → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {l3} {A} =
  type-subtype (is-discrete-Prop-Relaxed-Σ-Decomposition {l1} {l2} {l3} {A})
```

## Propositions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (D : Relaxed-Σ-Decomposition l2 l3 A)
  (is-discrete : is-discrete-Relaxed-Σ-Decomposition D)
  where

  equiv-discrete-is-discrete-Relaxed-Σ-Decomposition :
    equiv-Relaxed-Σ-Decomposition D (discrete-Relaxed-Σ-Decomposition l4 A)
  pr1 equiv-discrete-is-discrete-Relaxed-Σ-Decomposition =
    ( inv-equiv
      ( right-unit-law-Σ-is-contr is-discrete ∘e
        matching-correspondence-Relaxed-Σ-Decomposition D))
  pr1 (pr2 equiv-discrete-is-discrete-Relaxed-Σ-Decomposition) x =
    ( map-equiv (compute-raise-unit l4) ∘ terminal-map ,
      is-equiv-comp
        ( map-equiv (compute-raise-unit l4))
        ( terminal-map)
        ( is-equiv-terminal-map-is-contr (is-discrete x))
        ( is-equiv-map-equiv ( compute-raise-unit l4)))
  pr2 (pr2 equiv-discrete-is-discrete-Relaxed-Σ-Decomposition) a =
    eq-pair-Σ
      ( ap ( λ f → map-equiv f a)
        ( ( left-inverse-law-equiv
            ( equiv-pr1 is-discrete ∘e
              matching-correspondence-Relaxed-Σ-Decomposition D)) ∙
        ( ( inv
            ( right-inverse-law-equiv
              ( equiv-pr1 ( λ _ → is-contr-raise-unit)))))))
      ( eq-is-contr is-contr-raise-unit)

is-contr-type-discrete-Relaxed-Σ-Decomposition :
  {l1 l2 : Level} {A : UU l1} →
  is-contr (type-discrete-Relaxed-Σ-Decomposition {l1} {l1} {l2} {A})
pr1 ( is-contr-type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {A}) =
  ( discrete-Relaxed-Σ-Decomposition l2 A ,
    is-discrete-discrete-Relaxed-Σ-Decomposition)
pr2 ( is-contr-type-discrete-Relaxed-Σ-Decomposition {l1} {l2} {A}) =
  ( λ x →
    eq-type-subtype
      ( is-discrete-Prop-Relaxed-Σ-Decomposition)
      ( inv
        ( eq-equiv-Relaxed-Σ-Decomposition
          ( pr1 x)
          ( discrete-Relaxed-Σ-Decomposition l2 A)
          ( equiv-discrete-is-discrete-Relaxed-Σ-Decomposition
            ( pr1 x)
            ( pr2 x)))))
```
