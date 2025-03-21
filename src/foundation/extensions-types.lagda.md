# Extensions of types

```agda
module foundation.extensions-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `X`. An
{{#concept "extension" Disambiguation="type" Agda=extension-type}} of `X` is an
object in the [coslice](foundation.coslice.md) under `X`, i.e., it consists of a
type `Y` and a map `f : X → Y`.

In the above definition of extensions of types our aim is to capture the most
general concept of what it means to be an extension of a type. Similarly, in any
[category](category-theory.categories.md) we would say that an extension of an
object `X` consists of an object `Y` equipped with a morphism `f : X → Y`.

Our notion of extensions of types are not to be confused with extension types of
cubical type theory or
[extension types of simplicial type theory](https://arxiv.org/abs/1705.07442).

## Definitions

### Extensions of types

```agda
extension-type : {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
extension-type l2 X = Σ (UU l2) (λ Y → X → Y)

module _
  {l1 l2 : Level} {X : UU l1} (Y : extension-type l2 X)
  where

  type-extension-type : UU l2
  type-extension-type = pr1 Y

  inclusion-extension-type : X → type-extension-type
  inclusion-extension-type = pr2 Y
```

## Properties

### Characterization of identifications of extensions of types

```agda
equiv-extension-type :
  {l1 l2 l3 : Level} {X : UU l1} →
  extension-type l2 X →
  extension-type l3 X → UU (l1 ⊔ l2 ⊔ l3)
equiv-extension-type (Y , f) (Z , g) =
  Σ (Y ≃ Z) (λ e → coherence-triangle-maps g (map-equiv e) f)

module _
  {l1 l2 : Level} {X : UU l1}
  where

  id-equiv-extension-type : (U : extension-type l2 X) → equiv-extension-type U U
  id-equiv-extension-type U = id-equiv , refl-htpy

  equiv-eq-extension-type :
    (U V : extension-type l2 X) → U ＝ V → equiv-extension-type U V
  equiv-eq-extension-type U .U refl = id-equiv-extension-type U

  is-torsorial-equiv-extension-type :
    (U : extension-type l2 X) → is-torsorial (equiv-extension-type U)
  is-torsorial-equiv-extension-type U =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-extension-type U))
      ( type-extension-type U , id-equiv)
      (is-torsorial-htpy' (inclusion-extension-type U))

  is-equiv-equiv-eq-extension-type :
    (U V : extension-type l2 X) → is-equiv (equiv-eq-extension-type U V)
  is-equiv-equiv-eq-extension-type U =
    fundamental-theorem-id
      ( is-torsorial-equiv-extension-type U)
      ( equiv-eq-extension-type U)

  extensionality-extension-type :
    (U V : extension-type l2 X) → (U ＝ V) ≃ equiv-extension-type U V
  extensionality-extension-type U V =
    equiv-eq-extension-type U V , is-equiv-equiv-eq-extension-type U V

  eq-equiv-extension-type :
    (U V : extension-type l2 X) → equiv-extension-type U V → U ＝ V
  eq-equiv-extension-type U V =
    map-inv-equiv (extensionality-extension-type U V)
```

### If an extension is equivalent to an equivalence, then it is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  (U : extension-type l2 X) (V : extension-type l3 X)
  where

  is-equiv-inclusion-extension-type-equiv :
    equiv-extension-type U V →
    is-equiv (inclusion-extension-type V) →
    is-equiv (inclusion-extension-type U)
  is-equiv-inclusion-extension-type-equiv (e , H) =
    is-equiv-top-map-triangle
      ( inclusion-extension-type V)
      ( map-equiv e)
      ( inclusion-extension-type U)
      ( H)
      ( is-equiv-map-equiv e)

  is-equiv-inclusion-extension-type-equiv' :
    equiv-extension-type U V →
    is-equiv (inclusion-extension-type U) →
    is-equiv (inclusion-extension-type V)
  is-equiv-inclusion-extension-type-equiv' (e , H) u =
    is-equiv-left-map-triangle
      ( inclusion-extension-type V)
      ( map-equiv e)
      ( inclusion-extension-type U)
      ( H)
      ( u)
      ( is-equiv-map-equiv e)
```
