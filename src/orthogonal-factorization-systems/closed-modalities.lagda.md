# The closed modalities

```agda
module orthogonal-factorization-systems.closed-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.contractible-types
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.joins-of-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-subuniverses
open import orthogonal-factorization-systems.sigma-closed-reflective-subuniverses
```

</details>

## Idea

Given any proposition `Q`, the
[join](synthetic-homotopy-theory.joins-of-types.md) operation `Q *_` defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md). We
call these the **closed modalities**.

## Definition

```agda
operator-closed-modality :
  (l : Level) {lQ : Level} (Q : Prop lQ) → operator-modality l (l ⊔ lQ)
operator-closed-modality l Q A = type-Prop Q * A

unit-closed-modality :
  {l lQ : Level} (Q : Prop lQ) → unit-modality (operator-closed-modality l Q)
unit-closed-modality Q {A} = inr-join (type-Prop Q) A

is-closed-modal :
  {l lQ : Level} (Q : Prop lQ) → UU l → Prop (l ⊔ lQ)
pr1 (is-closed-modal Q A) = type-Prop Q → is-contr A
pr2 (is-closed-modal Q A) = is-prop-function-type is-property-is-contr
```

## Properties

### The closed modalities define `Σ`-closed reflective subuniverses

```agda
module _
  {l lQ : Level} (Q : Prop lQ)
  where

  is-reflective-subuniverse-closed-modality :
    is-reflective-subuniverse
      { l ⊔ lQ}
      ( unit-closed-modality Q)
      ( is-closed-modal Q)
  pr1 is-reflective-subuniverse-closed-modality A q =
    left-zero-law-join-is-contr
      ( type-Prop Q)
      ( A)
      ( is-proof-irrelevant-is-prop (is-prop-type-Prop Q) q)
  pr2 is-reflective-subuniverse-closed-modality X x Y =
    {!  !}

  reflective-subuniverse-closed-modality :
    reflective-subuniverse (l ⊔ lQ) (l ⊔ lQ)
  pr1 reflective-subuniverse-closed-modality =
    operator-closed-modality (l ⊔ lQ) Q
  pr1 (pr2 reflective-subuniverse-closed-modality) =
    unit-closed-modality Q
  pr1 (pr2 (pr2 reflective-subuniverse-closed-modality)) =
    is-closed-modal Q
  pr2 (pr2 (pr2 reflective-subuniverse-closed-modality)) =
    is-reflective-subuniverse-closed-modality

  is-Σ-closed-reflective-subuniverse-closed-modality :
    is-Σ-closed-reflective-subuniverse
      ( reflective-subuniverse-closed-modality)
  is-Σ-closed-reflective-subuniverse-closed-modality
    X is-modal-X P is-modal-P q =
    is-contr-Σ
      ( is-modal-X q)
      ( center (is-modal-X q))
      ( is-modal-P (center (is-modal-X q)) q)

  Σ-closed-reflective-subuniverse-closed-modality :
    Σ-closed-reflective-subuniverse (l ⊔ lQ) (l ⊔ lQ)
  pr1 Σ-closed-reflective-subuniverse-closed-modality =
    reflective-subuniverse-closed-modality
  pr2 Σ-closed-reflective-subuniverse-closed-modality =
    is-Σ-closed-reflective-subuniverse-closed-modality
```

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
