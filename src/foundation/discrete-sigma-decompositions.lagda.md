# Discrete Σ-Decompositions

```agda
module foundation.discrete-sigma-decompositions where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sigma-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
```

## Definition

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  discrete-Σ-Decomposition :
    Σ-Decomposition l1 lzero A
  pr1 discrete-Σ-Decomposition = A
  pr1 (pr2 discrete-Σ-Decomposition) a = ( unit , unit-trunc-Prop star)
  pr2 (pr2 discrete-Σ-Decomposition) = inv-equiv (equiv-pr1 λ _ → is-contr-unit)

module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  where

  is-discrete-Σ-Decomposition :
    UU (l2 ⊔ l3)
  is-discrete-Σ-Decomposition =
    (x : indexing-type-Σ-Decomposition D) → is-contr (cotype-Σ-Decomposition D x)
```

## Propositions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  (D : Σ-Decomposition l2 l3 A)
  (is-discrete : is-discrete-Σ-Decomposition D)
  where

  equiv-discrete-is-discrete-Σ-Decomposition :
    equiv-Σ-Decomposition D (discrete-Σ-Decomposition A)
  pr1 equiv-discrete-is-discrete-Σ-Decomposition =
    ( inv-equiv
      ( right-unit-law-Σ-is-contr is-discrete ∘e
        matching-correspondence-Σ-Decomposition D ))
  pr1 (pr2 equiv-discrete-is-discrete-Σ-Decomposition) x =
    ( terminal-map , is-equiv-terminal-map-is-contr (is-discrete x) )
  pr2 (pr2 equiv-discrete-is-discrete-Σ-Decomposition) a =
    eq-pair-Σ
      ( ap ( λ f → map-equiv f a)
        ( ( left-inverse-law-equiv
            ( equiv-pr1 is-discrete ∘e
              matching-correspondence-Σ-Decomposition D))  ∙
        ( ( inv
            ( right-inverse-law-equiv
              ( equiv-pr1 ( λ _ → is-contr-unit)))))))
      ( eq-is-contr is-contr-unit)
```

