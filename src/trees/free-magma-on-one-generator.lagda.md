# The free magma on one generator

```agda
module trees.free-magma-on-one-generator where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-binary-homotopies-binary-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications-dependent-functions
open import foundation.universe-levels

open import foundation-core.dependent-identifications

open import structured-types.magmas
open import structured-types.morphisms-magmas

open import trees.combinator-full-binary-trees
open import trees.full-binary-trees
```

</details>

## Idea

Function extensionality implies that the
[magma of full binary trees](trees.combinator-full-binary-trees.md) is the
**free magma on one generator**. That is, there are natural maps

```text
  ev-leaf-hom-Magma : hom-Magma full-binary-tree-Magma M → (type-Magma M)
  map-inv-ev-leaf-hom-Magma : (type-Magma M) → hom-Magma full-binary-tree-Magma M
```

for any [magma](structured-types.magmas.md) `M` that form an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The universal property of free magmas with one generator

```agda
module _
  {l : Level} (M : Magma l) (x : type-Magma M)
  where

  is-free-magma-on-one-generator : UUω
  is-free-magma-on-one-generator =
    {l2 : Level} (N : Magma l2) → is-equiv (ev-element-hom-Magma M N x)
```

## Proof

```agda
module _
  {l : Level} (M : Magma l)
  where

  ev-leaf-hom-Magma : hom-Magma full-binary-tree-Magma M → type-Magma M
  ev-leaf-hom-Magma (f , _) = f leaf-full-binary-tree

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

  map-inv-ev-leaf-hom-Magma :
    type-Magma M → hom-Magma full-binary-tree-Magma M
  pr1 (map-inv-ev-leaf-hom-Magma m) =
    extension-of-point-full-binary-tree-Magma m
  pr2 (map-inv-ev-leaf-hom-Magma m) =
    is-hom-extension-of-point-full-binary-tree-Magma m

  is-retraction-extension-of-point-full-binary-tree-Magma :
    ( T : full-binary-tree) → (f : hom-Magma full-binary-tree-Magma M) →
    extension-of-point-full-binary-tree-Magma (ev-leaf-hom-Magma f) T ＝
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

  dependent-identification-preserves-mul-full-binary-tree-Magma :
    ( f : hom-Magma full-binary-tree-Magma M) →
    dependent-identification (preserves-mul-Magma full-binary-tree-Magma M)
    ( eq-htpy
      ( λ T → is-retraction-extension-of-point-full-binary-tree-Magma T f))
    ( λ T U → refl) (pr2 f)
  dependent-identification-preserves-mul-full-binary-tree-Magma f =
    eq-binary-htpy _ _
      ( λ U V →
        ( htpy-eq
          ( tr-Π
            ( eq-htpy (λ T →
              is-retraction-extension-of-point-full-binary-tree-Magma T f))
            ( λ T U → refl)
            ( U))
          ( V)) ∙
        ( tr-Π
          ( eq-htpy (λ T →
            is-retraction-extension-of-point-full-binary-tree-Magma T f))
          ( λ U → refl)
          ( V)) ∙
        ( map-compute-dependent-identification-eq-value-function
          ( λ f → f (combinator-full-binary-tree U V))
          ( λ f → mul-Magma M (f U) (f V))
          ( eq-htpy
            ( λ T →
              is-retraction-extension-of-point-full-binary-tree-Magma T f))
          ( refl)
          ( preserves-mul-map-hom-Magma full-binary-tree-Magma M f U V)
          ( ( ap
              ( _∙ preserves-mul-map-hom-Magma full-binary-tree-Magma M f U V)
              ( htpy-eq (is-section-eq-htpy _) _)) ∙
            ( is-section-inv-concat'
              ( preserves-mul-map-hom-Magma full-binary-tree-Magma M f U V)
              ( _)) ∙
            ( ap-binary-htpy
              ( λ T →
                is-retraction-extension-of-point-full-binary-tree-Magma T f)
              ( mul-Magma M)))))

  is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma :
    is-equiv ev-leaf-hom-Magma
  pr1 (pr1 (is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma)) =
    map-inv-ev-leaf-hom-Magma
  pr2 (pr1 (is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma)) _ = refl
  pr1 (pr2 (is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma)) =
    map-inv-ev-leaf-hom-Magma
  pr2 (pr2 (is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma)) f =
    eq-pair-Σ (eq-htpy
      ( λ T → is-retraction-extension-of-point-full-binary-tree-Magma T f))
    ( dependent-identification-preserves-mul-full-binary-tree-Magma f)

  equiv-ev-leaf-hom-Magma-full-binary-tree-Magma :
    hom-Magma full-binary-tree-Magma M ≃ type-Magma M
  pr1 (equiv-ev-leaf-hom-Magma-full-binary-tree-Magma) = ev-leaf-hom-Magma
  pr2 (equiv-ev-leaf-hom-Magma-full-binary-tree-Magma) =
    is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma

is-free-magma-on-one-generator-full-binary-tree-Magma :
  is-free-magma-on-one-generator full-binary-tree-Magma leaf-full-binary-tree
is-free-magma-on-one-generator-full-binary-tree-Magma =
  is-equiv-ev-leaf-hom-Magma-full-binary-tree-Magma
```

## See also

- This construction may be extended to
  [labeled full binary trees](trees.labeled-full-binary-trees.md) to realize
  free magmas on any type, see
  [`trees.free-magmas-on-types`](trees.free-magmas-on-types.md).

## External links

[Free magmas](https://ncatlab.org/nlab/show/magma#free_magmas) at $n$Lab
