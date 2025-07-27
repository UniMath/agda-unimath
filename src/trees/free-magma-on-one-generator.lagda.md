# The free magma on one generator

```agda
module trees.free-magma-on-one-generator where
```

<details><summary>Imports</summary>

```agda
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
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.propositions
open import foundation-core.sets

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
`hom-Magma full-binary-tree-Magma M → M, M → hom-Magma full-binary-tree-Magma M`
for any [magma](structured-types.magmas.md) `M`, and when `M` is a set, we may
prove these form an equivalence.

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

  is-equiv-image-of-leaf : is-set (type-Magma M) → is-equiv image-of-leaf
  pr1 (pr1 (is-equiv-image-of-leaf _)) = extension-of-point-hom-full-binary-tree-Magma
  pr2 (pr1 (is-equiv-image-of-leaf _)) _ = refl
  pr1 (pr2 (is-equiv-image-of-leaf _)) = extension-of-point-hom-full-binary-tree-Magma
  pr2 (pr2 (is-equiv-image-of-leaf M-set)) (f , f-hom) =
    eq-pair-Σ (eq-htpy htpy) dep
    where
    htpy :
      pr1 (extension-of-point-hom-full-binary-tree-Magma
      ( image-of-leaf (f , f-hom))) ~ f
    htpy leaf-full-binary-tree = refl
    htpy (join-full-binary-tree L R) = inv {! f-hom L R  !}

    dep :
      dependent-identification (preserves-mul-Magma full-binary-tree-Magma M)
      ( eq-htpy htpy) (λ T U → refl) f-hom
    dep = {!   !}
```
