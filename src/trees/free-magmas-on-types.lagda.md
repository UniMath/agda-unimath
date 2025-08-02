# Free magmas on types

```agda
module trees.free-magmas-on-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
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

As the type of [full binary trees](trees.full-binary-trees.md) is the
[free magma on one generator](trees.free-magma-on-one-generator.md), so too is
the type of [labeled full binary trees](trees.labeled-full-binary-trees.md) with
indices labeled in a type `X` the **free magma on `X`**. The product comes from
the [combinator of full binary trees](trees.combinator-full-binary-trees.md).

What is meant by the "free magma on `X`" is the following. There are natural
maps
`label-of-leaf : hom-Magma (labeled-full-binary-tree-Magma X) M → (X → type-Magma M), extension-of-map-labeled-full-binary-tree-Magma : (X → type-Magma M) → labeled-full-binary-tree X → type-Magma M`
for any [magma](structured-types.magmas.md) `M` and type `X`.
`extension-of-map-labeled-full-binary-tree-Magma` is always a
[section](foundation-core.sections.md) of `label-of-leaf`, and when `M` is a
set, we may prove it is also a [retraction](foundation-core.retractions.md),
i.e. that `label-of-leaf` is an [equivalence](foundation-core.equivalences.md).

## Proof

```agda
module _
  {l1 l2 : Level} (X : UU l1) (M : Magma l2)
  where

  label-of-leaf :
    hom-Magma (labeled-full-binary-tree-Magma X) M → (X → type-Magma M)
  label-of-leaf (f , _) x = f (leaf-full-binary-tree , λ _ → x)

  {-# TERMINATING #-}
  extension-of-map-labeled-full-binary-tree-Magma :
    ( X → type-Magma M) → labeled-full-binary-tree X → type-Magma M
  extension-of-map-labeled-full-binary-tree-Magma
    f (leaf-full-binary-tree , label-T) = f (label-T star)
  extension-of-map-labeled-full-binary-tree-Magma
    f (join-full-binary-tree L R , label-T) = mul-Magma M
    ( extension-of-map-labeled-full-binary-tree-Magma f
      ( L , (λ x → label-T (inl x))))
    ( extension-of-map-labeled-full-binary-tree-Magma f
      ( R , (λ x → label-T (inr x))))

  is-hom-extension-of-map-labeled-full-binary-tree-Magma :
    ( f : X → type-Magma M) →
    preserves-mul-Magma (labeled-full-binary-tree-Magma X) M
    ( extension-of-map-labeled-full-binary-tree-Magma f)
  is-hom-extension-of-map-labeled-full-binary-tree-Magma _ _ _ = refl

  extension-of-map-hom-labeled-full-binary-tree-Magma :
    ( X → type-Magma M) → hom-Magma (labeled-full-binary-tree-Magma X) M
  extension-of-map-hom-labeled-full-binary-tree-Magma f =
    extension-of-map-labeled-full-binary-tree-Magma f ,
    is-hom-extension-of-map-labeled-full-binary-tree-Magma f

  {-# TERMINATING #-}
  is-retraction-extension-of-map-labeled-full-binary-tree-Magma :
    ( T : labeled-full-binary-tree X) →
    ( f : hom-Magma (labeled-full-binary-tree-Magma X) M) →
    extension-of-map-labeled-full-binary-tree-Magma (label-of-leaf f) T ＝
    map-hom-Magma (labeled-full-binary-tree-Magma X) M f T
  is-retraction-extension-of-map-labeled-full-binary-tree-Magma
    ( leaf-full-binary-tree , label-T) f = refl
  is-retraction-extension-of-map-labeled-full-binary-tree-Magma
    ( join-full-binary-tree L R , label-T) (f , is-hom-f) =
      ap-binary (mul-Magma M)
      ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma
        ( L , (λ x → label-T (inl x))) (f , is-hom-f))
      ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma
        ( R , (λ x → label-T (inr x))) (f , is-hom-f))
      ∙ inv (is-hom-f
        ( L , (λ x → label-T (inl x))) (R , (λ x → label-T (inr x))))
      ∙ ap f lem
        where
        lem :
          combinator-labeled-full-binary-tree X
          ( L , (λ x → label-T (inl x))) (R , (λ x → label-T (inr x))) ＝
          (( join-full-binary-tree L R) , label-T)
        lem = eq-pair-Σ refl (eq-htpy htpy)
          where
          htpy :
            tr (labeling-full-binary-tree X) refl (pr2
            ( combinator-labeled-full-binary-tree X
            ( L , (λ x → label-T (inl x))) (R , (λ x → label-T (inr x))))) ~
            label-T
          htpy (inl _) = refl
          htpy (inr _) = refl

  is-set-dependent-identification-preserves-mul-labeled-full-binary-tree-Magma :
    ( f : hom-Magma (labeled-full-binary-tree-Magma X) M) →
    is-set (type-Magma M) →
    dependent-identification
    ( preserves-mul-Magma (labeled-full-binary-tree-Magma X) M)
    (eq-htpy
    ( λ T → is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
    ( λ T U → refl) (pr2 f)
  is-set-dependent-identification-preserves-mul-labeled-full-binary-tree-Magma
    f is-set-M =
    eq-htpy htpy
    where
    htpy :
      tr (preserves-mul-Magma (labeled-full-binary-tree-Magma X) M)
      ( eq-htpy (λ T →
      is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
      ( λ T U → refl) ~ pr2 f
    htpy T = eq-htpy htpy2
      where
      htpy2 :
        tr (preserves-mul-Magma (labeled-full-binary-tree-Magma X) M) (eq-htpy
          ( λ U →
            is-retraction-extension-of-map-labeled-full-binary-tree-Magma U f))
        ( λ U V → refl) T ~ pr2 f T
      htpy2 U =
        pr1 (is-set-M (map-hom-Magma (labeled-full-binary-tree-Magma X) M f
          ( pr2 (labeled-full-binary-tree-Magma X) T U))
          ( pr2 M (map-hom-Magma (labeled-full-binary-tree-Magma X) M f T)
          ( map-hom-Magma (labeled-full-binary-tree-Magma X) M f U))
          ( tr (preserves-mul-Magma (labeled-full-binary-tree-Magma X) M)
          ( eq-htpy (λ V →
            is-retraction-extension-of-map-labeled-full-binary-tree-Magma V f))
          ( λ V W → refl) T U) (pr2 f T U))

  is-set-is-equiv-label-of-leaf-full-binary-tree-Magma :
    is-set (type-Magma M) → is-equiv label-of-leaf
  pr1 (pr1 (is-set-is-equiv-label-of-leaf-full-binary-tree-Magma _)) =
    extension-of-map-hom-labeled-full-binary-tree-Magma
  pr2 (pr1 (is-set-is-equiv-label-of-leaf-full-binary-tree-Magma _)) _ = refl
  pr1 (pr2 (is-set-is-equiv-label-of-leaf-full-binary-tree-Magma _)) =
    extension-of-map-hom-labeled-full-binary-tree-Magma
  pr2 (pr2 (is-set-is-equiv-label-of-leaf-full-binary-tree-Magma is-set-M)) f =
    eq-pair-Σ (eq-htpy (λ T →
    is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
    ( is-set-dependent-identification-preserves-mul-labeled-full-binary-tree-Magma
    f is-set-M)

  is-set-equiv-label-of-leaf-labeled-full-binary-tree-Magma :
    is-set (type-Magma M) →
    hom-Magma (labeled-full-binary-tree-Magma X) M ≃ (X → type-Magma M)
  pr1 (is-set-equiv-label-of-leaf-labeled-full-binary-tree-Magma _) =
    label-of-leaf
  pr2 (is-set-equiv-label-of-leaf-labeled-full-binary-tree-Magma is-set-M) =
    is-set-is-equiv-label-of-leaf-full-binary-tree-Magma is-set-M
```

## External links

[Free magmas](https://ncatlab.org/nlab/show/magma#free_magmas) at $n$Lab
