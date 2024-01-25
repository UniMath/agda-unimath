# Injective type families

```agda
module foundation.injective-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-function-types
open import foundation.iterated-dependent-product-types
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A type family `P : A → UU` is
{{#concept "injective" Disambiguation="type family"}} if it is
[injective as a map](foundation-core.injective-maps.md). However, we can also
consider injectivity with respect to
[equivalences of types](foundation-core.equivalences.md), which we dub
{{#concept "equivalence injectivity" Disambiguation="type family" Agda=is-equiv-injective}}.
By [univalence](foundation-core.univalence.md), these two structures are
equivalent, but more generally every equivalence injective type family must
always be injective as a map.

## Definition

### Equivalence injective type families

```agda
is-equiv-injective : {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-equiv-injective {A = A} P = {x y : A} → P x ≃ P y → x ＝ y
```

## Properties

### Equivalence injective type families are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  is-injective-is-equiv-injective : is-equiv-injective P → is-injective P
  is-injective-is-equiv-injective H = H ∘ equiv-eq

  is-equiv-injective-is-injective : is-injective P → is-equiv-injective P
  is-equiv-injective-is-injective H = H ∘ eq-equiv

  is-equiv-is-injective-is-equiv-injective :
    is-equiv is-injective-is-equiv-injective
  is-equiv-is-injective-is-equiv-injective =
    is-equiv-map-implicit-Π-is-fiberwise-equiv
      ( λ x →
        is-equiv-map-implicit-Π-is-fiberwise-equiv
          ( λ y →
            is-equiv-precomp-is-equiv
              ( equiv-eq)
              ( univalence (P x) (P y))
              ( x ＝ y)))

  equiv-is-injective-is-equiv-injective : is-equiv-injective P ≃ is-injective P
  pr1 equiv-is-injective-is-equiv-injective =
    is-injective-is-equiv-injective
  pr2 equiv-is-injective-is-equiv-injective =
    is-equiv-is-injective-is-equiv-injective

  equiv-is-equiv-injective-is-injective : is-injective P ≃ is-equiv-injective P
  equiv-is-equiv-injective-is-injective =
    inv-equiv equiv-is-injective-is-equiv-injective
```

### For a map between sets, being equivalence injective is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A) (P : A → UU l2)
  where

  is-prop-is-equiv-injective : is-prop (is-equiv-injective P)
  is-prop-is-equiv-injective =
    is-prop-iterated-implicit-Π 2 (λ x y → is-prop-function-type (is-set-A x y))

  is-equiv-injective-Prop : Prop (l1 ⊔ l2)
  pr1 is-equiv-injective-Prop = is-equiv-injective P
  pr2 is-equiv-injective-Prop = is-prop-is-equiv-injective
```
