# Orthogonal factorization systems

```agda
module orthogonal-factorization-systems.orthogonal-factorization-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorization-operations
open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.wide-function-classes
```

</details>

## Idea

An **orthogonal factorization system** is a pair of composition closed function
classes `L` and `R` that contain the identities (morally, this means that they
are wide subpre-∞-categories of the ∞-category of types), such that for every
function `f : A → B` there is a unique factorization `f ~ r ∘ l` such that the
left map (by diagrammatic ordering) `l` is in `L` and the right map `r` is in
`R`.

## Definition

### Orthogonal factorization systems

```agda
is-orthogonal-factorization-system :
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  → UU (lsuc l ⊔ lL ⊔ lR)
is-orthogonal-factorization-system {l} L R =
  ( is-wide-function-class L) ×
  ( ( is-wide-function-class R) ×
    ( (A B : UU l) → unique-function-class-factorization-operation L R A B))

orthogonal-factorization-system :
  (l lL lR : Level) → UU (lsuc l ⊔ lsuc lL ⊔ lsuc lR)
orthogonal-factorization-system l lL lR =
  Σ ( function-class l l lL)
    ( λ L →
      Σ ( function-class l l lR)
        ( is-orthogonal-factorization-system L))
```

## Properties

### Being an orthogonal factorization system is a property

```agda
module _
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  where

  is-prop-is-orthogonal-factorization-system :
    is-prop (is-orthogonal-factorization-system L R)
  is-prop-is-orthogonal-factorization-system =
    is-prop-prod
      ( is-prop-is-wide-function-class L)
      ( is-prop-prod
        ( is-prop-is-wide-function-class R)
        ( is-prop-Π
            λ A → is-prop-Π
              λ B → is-prop-unique-function-class-factorization-operation L R))

  is-orthogonal-factorization-system-Prop : Prop (lsuc l ⊔ lL ⊔ lR)
  pr1 is-orthogonal-factorization-system-Prop =
    is-orthogonal-factorization-system L R
  pr2 is-orthogonal-factorization-system-Prop =
    is-prop-is-orthogonal-factorization-system
```

## See also

The equivalent notions of

- [Higher modalities](orthogonal-factorization-systems.higher-modalities.md)
- [Uniquely eliminating modalities](orthogonal-factorization-systems.uniquely-eliminating-modalities.md)
- [Σ-closed reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
