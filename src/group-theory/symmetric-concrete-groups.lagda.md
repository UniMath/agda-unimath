# Symmetric concrete groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.symmetric-concrete-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.mere-equality funext
open import foundation.sets funext
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.automorphism-groups funext
open import group-theory.concrete-groups funext
```

</details>

## Idea

The **symmetric concrete group** of a [set](foundation-core.sets.md) `X` is the
[connected component](foundation.connected-components-universes.md) of the
universe of sets at `X`.

## Definition

```agda
module _
  {l : Level} (A : Set l)
  where

  classifying-type-symmetric-Concrete-Group : UU (lsuc l)
  classifying-type-symmetric-Concrete-Group =
    classifying-type-Automorphism-Group (Set-1-Type l) A

  shape-symmetric-Concrete-Group : classifying-type-symmetric-Concrete-Group
  shape-symmetric-Concrete-Group = shape-Automorphism-Group (Set-1-Type l) A

  symmetric-Concrete-Group : Concrete-Group (lsuc l)
  symmetric-Concrete-Group = Automorphism-Group (Set-1-Type l) A
```

## Properties

### Characterizing equality of the classifying type of the symmetric concrete groups

```agda
module _
  {l : Level} (A : Set l)
  where

  equiv-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) → UU l
  equiv-classifying-type-symmetric-Concrete-Group X Y =
    equiv-Set (pr1 X) (pr1 Y)

  type-symmetric-Concrete-Group : UU l
  type-symmetric-Concrete-Group =
    equiv-classifying-type-symmetric-Concrete-Group
      ( shape-symmetric-Concrete-Group A)
      ( shape-symmetric-Concrete-Group A)

  extensionality-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) →
    (X ＝ Y) ≃ equiv-classifying-type-symmetric-Concrete-Group X Y
  extensionality-classifying-type-symmetric-Concrete-Group X =
    extensionality-type-subtype
      ( λ Y → mere-eq-Prop Y A)
      ( pr2 X)
      ( id-equiv)
      ( extensionality-Set (pr1 X))

  equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X Y : classifying-type-symmetric-Concrete-Group A) →
    (X ＝ Y) → equiv-classifying-type-symmetric-Concrete-Group X Y
  equiv-eq-classifying-type-symmetric-Concrete-Group X Y =
    map-equiv (extensionality-classifying-type-symmetric-Concrete-Group X Y)

  refl-equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X : classifying-type-symmetric-Concrete-Group A) →
    equiv-eq-classifying-type-symmetric-Concrete-Group X X refl ＝ id-equiv
  refl-equiv-eq-classifying-type-symmetric-Concrete-Group X = refl

  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Group :
    (X Y Z : classifying-type-symmetric-Concrete-Group A)
    (q : Y ＝ Z) (p : X ＝ Y) →
    equiv-eq-classifying-type-symmetric-Concrete-Group X Z (p ∙ q) ＝
    ( ( equiv-eq-classifying-type-symmetric-Concrete-Group Y Z q) ∘e
      ( equiv-eq-classifying-type-symmetric-Concrete-Group X Y p))
  preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Group
    X .X Z q refl =
    inv
      ( right-unit-law-equiv
        ( equiv-eq-classifying-type-symmetric-Concrete-Group X Z q))
```

### Equivalent sets have isomorphic symmetric concrete groups

This remains to be shown.
[#737](https://github.com/UniMath/agda-unimath/issues/737)
