# Free magmas on types

```agda
module trees.free-magmas-on-types where
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
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications-dependent-functions
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

```text
  ev-label-leaf-hom-Magma : hom-Magma (labeled-full-binary-tree-Magma X) M → (X → type-Magma M)
  map-inv-ev-label-leaf-hom-Magma : (X → type-Magma M) → labeled-full-binary-tree X → type-Magma M
```

for any [magma](structured-types.magmas.md) `M` and type `X` that form an
[equivalence](foundation-core.equivalences.md).

## Definition

### The universal property of free magmas on types

```agda
module _
  {l1 l2 : Level} (M : Magma l1) (X : UU l2) (f : X → type-Magma M)
  where

  is-free-magma-on-type : UUω
  is-free-magma-on-type =
    {l3 : Level} (N : Magma l3) → is-equiv (λ g → map-hom-Magma M N g ∘ f)
```

## Proof

```agda
module _
  {l1 l2 : Level} (X : UU l1) (M : Magma l2)
  where

  ev-label-leaf-hom-Magma :
    hom-Magma (labeled-full-binary-tree-Magma X) M → (X → type-Magma M)
  ev-label-leaf-hom-Magma (f , _) x = f (leaf-full-binary-tree , λ _ → x)

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

  map-inv-ev-label-leaf-hom-Magma :
    ( X → type-Magma M) → hom-Magma (labeled-full-binary-tree-Magma X) M
  map-inv-ev-label-leaf-hom-Magma f =
    extension-of-map-labeled-full-binary-tree-Magma f ,
    is-hom-extension-of-map-labeled-full-binary-tree-Magma f

  {-# TERMINATING #-}
  is-retraction-extension-of-map-labeled-full-binary-tree-Magma :
    ( T : labeled-full-binary-tree X) →
    ( f : hom-Magma (labeled-full-binary-tree-Magma X) M) →
    extension-of-map-labeled-full-binary-tree-Magma
      ( ev-label-leaf-hom-Magma f) T ＝
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
      ∙ ap f (combinator-commutes-with-labelings-full-binary-tree X L R label-T)

  dependent-identification-preserves-mul-labeled-full-binary-tree-Magma :
    ( f : hom-Magma (labeled-full-binary-tree-Magma X) M) →
    dependent-identification
    ( preserves-mul-Magma (labeled-full-binary-tree-Magma X) M)
    ( eq-htpy
    ( λ T → is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
    ( λ T U → refl) (pr2 f)
  dependent-identification-preserves-mul-labeled-full-binary-tree-Magma f =
    eq-binary-htpy _ _ (λ U V → htpy-eq
      ( tr-Π (eq-htpy
        ( λ T →
          is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
        ( λ T U → refl) U) V ∙ tr-Π (eq-htpy
        ( λ T →
          is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
      ( λ U → refl) V ∙ (map-compute-dependent-identification-eq-value-function
      ( λ f → f (combinator-labeled-full-binary-tree X U V))
      ( λ f → mul-Magma M (f U) (f V))
      ( eq-htpy
        ( λ T →
          is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
      ( refl)
      ( pr2 f U V)
      ( ap (λ p → p ∙ pr2 f U V) (htpy-eq (is-section-eq-htpy
        ( λ T →
          is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
        ( combinator-labeled-full-binary-tree X U V)) ∙
      ( ap (λ p → ap-binary (pr2 M)
        ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma
          ( pr1 U , (λ x → pr2 U x)) (pr1 f , pr2 f))
        ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma
          ( pr1 V , (λ x → pr2 V x)) (pr1 f , pr2 f))
        ∙ inv (pr2 f (pr1 U , (λ x → pr2 U x)) (pr1 V , (λ x → pr2 V x)))
        ∙ p ∙ pr2 f U V) {!   !} ∙ {!   !} ∙
          is-section-inv-concat' (pr2 f U V) (ap-binary (pr2 M)
        ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma U f)
        ( is-retraction-extension-of-map-labeled-full-binary-tree-Magma V f))) ∙
      ap-binary-htpy
      ( λ T → is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f)
      ( mul-Magma M))))

  is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma :
    is-equiv ev-label-leaf-hom-Magma
  pr1 (pr1 (is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma)) =
    map-inv-ev-label-leaf-hom-Magma
  pr2 (pr1 (is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma)) _ = refl
  pr1 (pr2 (is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma)) =
    map-inv-ev-label-leaf-hom-Magma
  pr2 (pr2 (is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma)) f =
    eq-pair-Σ (eq-htpy (λ T →
    is-retraction-extension-of-map-labeled-full-binary-tree-Magma T f))
    ( dependent-identification-preserves-mul-labeled-full-binary-tree-Magma f)

  equiv-ev-label-leaf-hom-Magma-labeled-full-binary-tree-Magma :
    hom-Magma (labeled-full-binary-tree-Magma X) M ≃ (X → type-Magma M)
  pr1 (equiv-ev-label-leaf-hom-Magma-labeled-full-binary-tree-Magma) =
    ev-label-leaf-hom-Magma
  pr2 (equiv-ev-label-leaf-hom-Magma-labeled-full-binary-tree-Magma) =
    is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma

is-free-magma-on-type-labeled-full-binary-tree-Magma :
  {l : Level} (X : UU l) → is-free-magma-on-type
  ( labeled-full-binary-tree-Magma X) X
  ( λ x → leaf-full-binary-tree , λ _ → x)
is-free-magma-on-type-labeled-full-binary-tree-Magma X =
  is-equiv-ev-label-leaf-hom-Magma-full-binary-tree-Magma X
```

## External links

[Free magmas](https://ncatlab.org/nlab/show/magma#free_magmas) at $n$Lab
