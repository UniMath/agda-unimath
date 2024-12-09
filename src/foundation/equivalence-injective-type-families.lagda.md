# Equivalence injective type families

```agda
module foundation.equivalence-injective-type-families where
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

We say a type family `P` is
{{#concept "equivalence injective" Disambiguation="type family" Agda=is-equivalence-injective}}
if for every [equivalence of types](foundation-core.equivalences.md) `P x ≃ P y`
we have `x ＝ y `. By [univalence](foundation-core.univalence.md), the
[structure](foundation.structure.md) of being equivalence injective is
equivalent to being [injective as a map](foundation-core.injective-maps.md), but
more generally every equivalence injective type family must always be injective
as a map.

**Note.** The concept of equivalence injective type family as considered here is
unrelated to the concept of "injective type" as studied by Martín Escardó in
_Injective types in univalent mathematics_ {{#cite Esc21b}}.

## Definition

### Equivalence injective type families

```agda
is-equivalence-injective :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-equivalence-injective {A = A} P = {x y : A} → P x ≃ P y → x ＝ y
```

## Properties

### Equivalence injective type families are injective as maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  is-injective-is-equivalence-injective :
    is-equivalence-injective P → is-injective P
  is-injective-is-equivalence-injective H = H ∘ equiv-eq

  is-equivalence-injective-is-injective :
    is-injective P → is-equivalence-injective P
  is-equivalence-injective-is-injective H = H ∘ eq-equiv

  is-equiv-is-injective-is-equivalence-injective :
    is-equiv is-injective-is-equivalence-injective
  is-equiv-is-injective-is-equivalence-injective =
    is-equiv-map-implicit-Π-is-fiberwise-equiv
      ( λ x →
        is-equiv-map-implicit-Π-is-fiberwise-equiv
          ( λ y →
            is-equiv-precomp-is-equiv
              ( equiv-eq)
              ( univalence (P x) (P y))
              ( x ＝ y)))

  equiv-is-injective-is-equivalence-injective :
    is-equivalence-injective P ≃ is-injective P
  pr1 equiv-is-injective-is-equivalence-injective =
    is-injective-is-equivalence-injective
  pr2 equiv-is-injective-is-equivalence-injective =
    is-equiv-is-injective-is-equivalence-injective

  equiv-is-equivalence-injective-is-injective :
    is-injective P ≃ is-equivalence-injective P
  equiv-is-equivalence-injective-is-injective =
    inv-equiv equiv-is-injective-is-equivalence-injective
```

### For a type family over a set, being equivalence injective is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A) (P : A → UU l2)
  where

  is-prop-is-equivalence-injective : is-prop (is-equivalence-injective P)
  is-prop-is-equivalence-injective =
    is-prop-iterated-implicit-Π 2 (λ x y → is-prop-function-type (is-set-A x y))

  is-equivalence-injective-Prop : Prop (l1 ⊔ l2)
  pr1 is-equivalence-injective-Prop = is-equivalence-injective P
  pr2 is-equivalence-injective-Prop = is-prop-is-equivalence-injective
```

## References

{{#bibliography}}
