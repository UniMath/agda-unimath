# Crisp function types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.action-on-identifications-flat-modality
open import modal-type-theory.crisp-dependent-function-types
open import modal-type-theory.flat-modality
open import modal-type-theory.functoriality-flat-modality
```

</details>

## Idea

We say a [function type](foundation-core.function-types.md) is
{{#concept "crisp" Disambiguation="function type"}} if it is formed in a
[crisp context](modal-type-theory.crisp-types.md).

A function `f` from `A` to `B` may be assumed to be a
{{#concept "crisp function" Disambiguation="of crisp types"}} given that its
domain and codomain are crisp. By this we mean it is a crisp element of its
type, written `@♭ f : A → B`. We may also assume that a function is
{{#concept "defined on crisp elements" Disambiguation="function on a crisp type"}}
if its definition assumes that the elements of its domain are crisp, written
`f : @♭ A → B`. Being crisp, and being defined on crisp elements are independent
properties. A function may be crisp and defined on cohesive elements, and it may
be cohesive but defined on crisp elements. Indeed, all configurations are
possible when both `A` and `B` are crisp:

|                              |  Crisp function | Cohesive function |
| ---------------------------: | --------------: | ----------------: |
|    Defined on crisp elements | `@♭ (@♭ A → B)` |        `@♭ A → B` |
| Defined on cohesive elements |    `@♭ (A → B)` |           `A → B` |

Note, since assuming that a hypothesis is crisp is _less_ general, assuming that
a hypothesis assumes that a hypothesis is crisp is _more_ general. Hence
assuming the function is cohesive and defined on crisp elements `f : @♭ A → B`
is the _weakest_ assumption one can make given that `A` is crisp, while assuming
it is crisp and defined on cohesive elements `@♭ f : A → B` is the strongest,
given that `B` is also crisp.

## Properties

### Flat distributes in one direction over function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-distributive-flat-crisp-function-types : ♭ (@♭ A → B) → (@♭ A → ♭ B)
  map-distributive-flat-crisp-function-types = map-distributive-flat-crisp-Π

  map-distributive-flat-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-flat-function-types f (intro-flat x) =
    map-distributive-flat-Π f (intro-flat x)
```

### Postcomposition by the flat counit induces an equivalence `♭ (♭ A → ♭ B) ≃ ♭ (♭ A → B)`

This is Theorem 6.14 in {{#cite Shu18}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-inv-action-flat-map-postcomp-counit-flat : ♭ (♭ A → B) → ♭ (♭ A → ♭ B)
  map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    intro-flat (λ where (intro-flat y) → intro-flat (f (intro-flat y)))

  is-section-map-inv-action-flat-map-postcomp-counit-flat :
    is-section
      ( action-flat-map (postcomp (♭ A) counit-flat))
      ( map-inv-action-flat-map-postcomp-counit-flat)
  is-section-map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    ap-flat (eq-htpy (λ where (intro-flat _) → refl))

  is-retraction-map-inv-action-flat-map-postcomp-counit-flat :
    is-retraction
      ( action-flat-map (postcomp (♭ A) counit-flat))
      ( map-inv-action-flat-map-postcomp-counit-flat)
  is-retraction-map-inv-action-flat-map-postcomp-counit-flat (intro-flat f) =
    ap-flat
      ( eq-htpy
        ( λ where
          (intro-flat x) → is-crisp-retraction-intro-flat (f (intro-flat x))))

  is-equiv-action-flat-map-postcomp-counit-flat :
    is-equiv (action-flat-map (postcomp (♭ A) (counit-flat {A = B})))
  is-equiv-action-flat-map-postcomp-counit-flat =
    is-equiv-is-invertible
      ( map-inv-action-flat-map-postcomp-counit-flat)
      ( is-section-map-inv-action-flat-map-postcomp-counit-flat)
      ( is-retraction-map-inv-action-flat-map-postcomp-counit-flat)

  equiv-action-flat-map-postcomp-counit-flat : ♭ (♭ A → ♭ B) ≃ ♭ (♭ A → B)
  pr1 equiv-action-flat-map-postcomp-counit-flat =
    action-flat-map (postcomp (♭ A) counit-flat)
  pr2 equiv-action-flat-map-postcomp-counit-flat =
    is-equiv-action-flat-map-postcomp-counit-flat
```

## See also

- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for crisp types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}
