# Reflective subuniverses

```agda
module orthogonal-factorization-systems.reflective-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

A **reflective subuniverse** is a subuniverse `P` together with a modal operator
`○` such that `○ A` is in `P` for all small types `A` and a modal unit with the
property that the types in `P` are local at the modal unit of all small types
`A`.

Hence the modal types with respect to `○` are precisely the types in the
reflective subuniverse.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {○ : modal-operator (l1 ⊔ l2) l1} (unit-○ : modal-unit ○)
  (is-modal' : UU (l1 ⊔ l2) → Prop l3)
  where

  is-reflective-subuniverse : UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
  is-reflective-subuniverse =
    ( (X : UU (l1 ⊔ l2)) → type-Prop (is-modal' (raise (l1 ⊔ l2) (○ X)))) ×
    ( (X : UU (l1 ⊔ l2)) → type-Prop (is-modal' X) →
      (Y : UU (l1 ⊔ l2)) → is-local-type (unit-○ {Y}) X)

reflective-subuniverse : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
reflective-subuniverse l1 l2 l3 =
  Σ ( modal-operator (l1 ⊔ l2) l1)
    ( λ ○ →
      Σ ( modal-unit ○)
        ( λ unit-○ →
          Σ ( UU (l1 ⊔ l2) → Prop l3)
            ( is-reflective-subuniverse {l1} {l2} {l3} unit-○)))

is-Σ-closed-reflective-subuniverse :
  {l1 l2 l3 : Level}
  (U : reflective-subuniverse l1 l2 l3) → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
is-Σ-closed-reflective-subuniverse (○ , unit-○ , is-modal' , _) =
  is-Σ-closed-modal-operator (type-Prop ∘ is-modal')

Σ-closed-reflective-subuniverse :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Σ-closed-reflective-subuniverse l1 l2 l3 =
  Σ ( reflective-subuniverse l1 l2 l3)
    ( is-Σ-closed-reflective-subuniverse {l1} {l2} {l3})
```

## See also

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Orthogonal factorization systems](orthogonal-factorization-systems.orthogonal-factorization-systems.md)

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020 ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526), [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
