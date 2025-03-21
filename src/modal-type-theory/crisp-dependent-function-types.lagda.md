# Crisp dependent function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [dependent function type](foundation.dependent-function-types.md) is
{{#concept "crisp" Disambiguation="dependent function type"}} if it is formed in
a [crisp context](modal-type-theory.crisp-types.md).

A dependent function `f` from `A` to `B` may be assumed to be a
{{#concept "crisp dependent function" Disambiguation="of crisp types"}} given
that its domain and codomain are crisp. By this we mean it is a crisp element of
its type, written `@♭ f : (x : A) → B x`. We may also assume that a dependent
function is
{{#concept "defined on crisp elements" Disambiguation="dependent function on a crisp type"}}
if its definition assumes that the elements of its domain are crisp, written
`f : (@♭ x : A) → B x`. Being crisp, and being defined on crisp elements are
independent properties. A dependent function may be crisp and defined on
cohesive elements, and it may be cohesive but defined on crisp elements. Indeed,
all configurations are possible when both `A` and `B` are crisp:

|                              | Crisp dependent function | Cohesive dependent function |
| ---------------------------: | -----------------------: | --------------------------: |
|    Defined on crisp elements |  `@♭ ((@♭ x : A) → B x)` |          `(@♭ x : A) → B x` |
| Defined on cohesive elements |     `@♭ ((x : A) → B x)` |             `(x : A) → B x` |

Note, since assuming that a hypothesis is crisp is _less_ general, assuming that
a hypothesis assumes that a hypothesis is crisp is _more_ general. Hence
assuming the dependent function is cohesive and defined on crisp elements
`f : (@♭ x : A) → B x` is the _weakest_ assumption one can make given that `A`
is crisp, while assuming the dependent function is crisp and defined on cohesive
elements `@♭ f : (x : A) → B x` is the strongest, given that `B` is also crisp.

## Properties

### Flat distributes in one direction over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  map-distributive-flat-crisp-Π : ♭ ((@♭ x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-distributive-flat-crisp-Π (intro-flat f) x = intro-flat (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Π :
    ♭ ((x : A) → B x) → ((x : ♭ A) → action-flat-family B x)
  map-distributive-flat-Π (intro-flat f) (intro-flat x) = intro-flat (f x)
```

### Postcomposition by the flat counit induces an equivalence under the flat modality on dependent function types

This is Theorem 6.14 in {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  map-action-flat-dependent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → action-flat-crisp-family B u) →
    ♭ ((u : ♭ A) → family-over-flat B u)
  map-action-flat-dependent-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat x) → counit-flat (f (intro-flat x)))

  map-inv-action-flat-dependent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → family-over-flat B u) →
    ♭ ((u : ♭ A) → action-flat-crisp-family B u)
  map-inv-action-flat-dependent-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat y) → intro-flat (f (intro-flat y)))

  is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat :
    is-section
      ( map-action-flat-dependent-map-postcomp-counit-flat)
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
  is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat
    (intro-flat f) =
    ap-flat (eq-htpy (λ where (intro-flat x) → refl))

  is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat :
    is-retraction
      ( map-action-flat-dependent-map-postcomp-counit-flat)
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
  is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat
    (intro-flat f) =
    ap-flat
      ( eq-htpy
        ( λ where
          (intro-flat x) → is-crisp-retraction-intro-flat (f (intro-flat x))))

  is-equiv-action-flat-depdendent-map-postcomp-counit-flat :
    is-equiv map-action-flat-dependent-map-postcomp-counit-flat
  is-equiv-action-flat-depdendent-map-postcomp-counit-flat =
    is-equiv-is-invertible
      ( map-inv-action-flat-dependent-map-postcomp-counit-flat)
      ( is-section-map-inv-action-flat-dependent-map-postcomp-counit-flat)
      ( is-retraction-map-inv-action-flat-dependent-map-postcomp-counit-flat)

  equiv-action-flat-depdendent-map-postcomp-counit-flat :
    ♭ ((u : ♭ A) → action-flat-crisp-family B u) ≃
    ♭ ((u : ♭ A) → family-over-flat B u)
  equiv-action-flat-depdendent-map-postcomp-counit-flat =
    ( map-action-flat-dependent-map-postcomp-counit-flat ,
      is-equiv-action-flat-depdendent-map-postcomp-counit-flat)
```

## See also

- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for crisp types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
