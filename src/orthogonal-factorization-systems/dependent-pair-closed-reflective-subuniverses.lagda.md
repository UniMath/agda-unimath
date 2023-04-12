# Dependent-pair-closed reflective subuniverses

```agda
module orthogonal-factorization-systems.dependent-pair-closed-reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.reflective-subuniverses
```

</details>

## Idea

A reflective subuniverse is **dependent-pair-closed** (or **Σ-closed**) if its
modal types are closed under the formation of dependent pair types.

## Definition

```agda
is-Σ-closed-reflective-subuniverse :
  {l lM : Level} (U : reflective-subuniverse l lM) → UU (lsuc l ⊔ lM)
is-Σ-closed-reflective-subuniverse (○ , unit-○ , is-modal' , _) =
  is-Σ-closed-modal-operator (type-Prop ∘ is-modal')

Σ-closed-reflective-subuniverse :
  (l lM : Level) → UU (lsuc l ⊔ lsuc lM)
Σ-closed-reflective-subuniverse l lM =
  Σ ( reflective-subuniverse l lM)
    ( is-Σ-closed-reflective-subuniverse)
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Orthogonal factorization systems](orthogonal-factorization-systems.orthogonal-factorization-systems.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
