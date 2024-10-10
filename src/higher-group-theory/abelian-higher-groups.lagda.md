# Abelian higher groups

```agda
module higher-group-theory.abelian-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.small-types
open import foundation.universe-levels

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups
open import higher-group-theory.small-higher-groups

open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.small-pointed-types

open import synthetic-homotopy-theory.connective-spectra
```

</details>

## Idea

An {{#concept "abelian" Disambiguation="∞-group"}}, or
{{#concept "commutative" Disambiguation="∞-group"}} ∞-group is a
[higher group](higher-group-theory.higher-groups.md) `A₀` that is commutative in
a fully coherent way. This may be expressed by saying that there exists a
[connective spectrum](synthetic-homotopy-theory.connective-spectra.md) such that
the ∞-group is the first type in the sequence. I.e., there exists a sequence of
increasingly [connected](foundation.connected-types.md) ∞-groups

```text
  A₀   A₁   A₂   A₃   ⋯   Aᵢ   ⋯
```

such that

```text
  Aᵢ ≃∗ Ω Aᵢ₊₁
```

Abelian ∞-groups thus give an example of another infinitely coherent structure
that is definable in Homotopy Type Theory.

## Definitions

### The predicate of being abelian with respect to a universe level

```agda
is-abelian-level-∞-Group :
  {l : Level} (l1 : Level) → ∞-Group l → UU (l ⊔ lsuc l1)
is-abelian-level-∞-Group l1 G =
  Σ ( Connective-Spectrum l1)
    ( λ A → pointed-type-∞-Group G ≃∗ pointed-type-Connective-Spectrum A 0)
```

### The predicate of being abelian

```agda
is-abelian-∞-Group : {l : Level} → ∞-Group l → UU (lsuc l)
is-abelian-∞-Group {l} G = is-abelian-level-∞-Group l G
```

## External links

- [abelian infinity-group](https://ncatlab.org/nlab/show/abelian+infinity-group)
  at $n$Lab
