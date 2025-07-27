# The free magma on one generator

```agda
module trees.free-magma-on-one-generator where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.function-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications

open import structured-types.magmas
open import structured-types.morphisms-magmas

open import trees.combinator-full-binary-trees
open import trees.full-binary-trees
open import trees.labeled-full-binary-trees
```

</details>

## Idea

Function extensionality implies that the
[magma of full binary trees](trees.combinator-full-binary-trees.md) is the
**free magma on one generator**. That is, there are natural maps
`image-of-leaf : hom-Magma full-binary-tree-Magma M → M, extension-of-point-hom-full-binary-tree-Magma : M → hom-Magma full-binary-tree-Magma M`
for any [magma](structured-types.magmas.md) `M`.
`extension-of-point-hom-full-binary-tree-Magma` is always a
[section](foundation-core.sections.md) of `image-of-leaf`, and when `M` is a
set, we may prove it is also a [retraction](foundation-core.retractions.md),
i.e. that `image-of-leaf` is an [equivalence](foundation-core.equivalences.md).

## Proof

```agda
module _
  {l : Level} (M : Magma l)
  where

  image-of-leaf : hom-Magma full-binary-tree-Magma M → type-Magma M
  image-of-leaf (f , _) = f leaf-full-binary-tree

  extension-of-point-full-binary-tree-Magma :
    type-Magma M → full-binary-tree → type-Magma M
  extension-of-point-full-binary-tree-Magma m leaf-full-binary-tree = m
  extension-of-point-full-binary-tree-Magma m (join-full-binary-tree L R) =
    mul-Magma M (extension-of-point-full-binary-tree-Magma m L)
    ( extension-of-point-full-binary-tree-Magma m R)

  is-hom-extension-of-point-full-binary-tree-Magma :
    ( m : type-Magma M) → preserves-mul-Magma full-binary-tree-Magma M
    ( extension-of-point-full-binary-tree-Magma m)
  is-hom-extension-of-point-full-binary-tree-Magma m T U = refl

  extension-of-point-hom-full-binary-tree-Magma :
    type-Magma M → hom-Magma full-binary-tree-Magma M
  pr1 (extension-of-point-hom-full-binary-tree-Magma m) =
    extension-of-point-full-binary-tree-Magma m
  pr2 (extension-of-point-hom-full-binary-tree-Magma m) =
    is-hom-extension-of-point-full-binary-tree-Magma m

  is-retraction-extension-of-point-full-binary-tree-Magma :
    ( T : full-binary-tree) → (f : hom-Magma full-binary-tree-Magma M) →
    extension-of-point-full-binary-tree-Magma (image-of-leaf f) T ＝
    map-hom-Magma full-binary-tree-Magma M f T
  is-retraction-extension-of-point-full-binary-tree-Magma
    leaf-full-binary-tree f = refl
  is-retraction-extension-of-point-full-binary-tree-Magma
    ( join-full-binary-tree L R) (f , is-hom-f) =
      ap-binary (mul-Magma M)
      ( is-retraction-extension-of-point-full-binary-tree-Magma L
        ( f , is-hom-f))
      ( is-retraction-extension-of-point-full-binary-tree-Magma R
        ( f , is-hom-f))
      ∙ inv (is-hom-f L R)

  is-set-dependent-identification-preserves-mul-full-binary-tree-Magma :
    ( f : hom-Magma full-binary-tree-Magma M) → is-set (type-Magma M) →
    dependent-identification (preserves-mul-Magma full-binary-tree-Magma M)
    ( eq-htpy
      ( λ T → is-retraction-extension-of-point-full-binary-tree-Magma T f))
    ( λ T U → refl) (pr2 f)
  is-set-dependent-identification-preserves-mul-full-binary-tree-Magma
    f is-set-M = eq-htpy htpy
      where
      htpy :
        tr (preserves-mul-Magma full-binary-tree-Magma M) (eq-htpy
          ( λ T → is-retraction-extension-of-point-full-binary-tree-Magma T f))
        ( λ T U → refl) ~ pr2 f
      htpy T = eq-htpy htpy2
        where
        htpy2 :
          tr (preserves-mul-Magma full-binary-tree-Magma M) (eq-htpy
            ( λ U → is-retraction-extension-of-point-full-binary-tree-Magma U f))
          ( λ U V → refl) T ~ pr2 f T
        htpy2 U =
          pr1 (is-set-M (map-hom-Magma full-binary-tree-Magma M f
            ( pr2 full-binary-tree-Magma T U))
              ( pr2 M (map-hom-Magma full-binary-tree-Magma M f T)
            ( map-hom-Magma full-binary-tree-Magma M f U))
              ( tr (preserves-mul-Magma full-binary-tree-Magma M)
            ( eq-htpy (λ V →
              is-retraction-extension-of-point-full-binary-tree-Magma V f))
            ( λ V W → refl) T U) (pr2 f T U))

  is-set-is-equiv-image-of-leaf-full-binary-tree-Magma :
    is-set (type-Magma M) → is-equiv image-of-leaf
  pr1 (pr1 (is-set-is-equiv-image-of-leaf-full-binary-tree-Magma _)) =
    extension-of-point-hom-full-binary-tree-Magma
  pr2 (pr1 (is-set-is-equiv-image-of-leaf-full-binary-tree-Magma _)) _ = refl
  pr1 (pr2 (is-set-is-equiv-image-of-leaf-full-binary-tree-Magma _)) =
    extension-of-point-hom-full-binary-tree-Magma
  pr2 (pr2 (is-set-is-equiv-image-of-leaf-full-binary-tree-Magma is-set-M)) f =
    eq-pair-Σ (eq-htpy
      ( λ T → is-retraction-extension-of-point-full-binary-tree-Magma T f))
    ( is-set-dependent-identification-preserves-mul-full-binary-tree-Magma
      f is-set-M)

  is-set-equiv-image-of-leaf-full-binary-tree-Magma :
    is-set (type-Magma M) → hom-Magma full-binary-tree-Magma M ≃ type-Magma M
  pr1 (is-set-equiv-image-of-leaf-full-binary-tree-Magma _) = image-of-leaf
  pr2 (is-set-equiv-image-of-leaf-full-binary-tree-Magma is-set-M) =
    is-set-is-equiv-image-of-leaf-full-binary-tree-Magma is-set-M
```
