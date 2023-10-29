# Homotopies of binary operations

```agda
module foundation.binary-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Consider two binary operations `f g : (x : A) (y : B x) → C x y`. The type of
**binary homotopies** between `f` and `g` is defined to be the type of pointwise
[identifications](foundation-core.identity-types.md) of `f` and `g`. We show
that this characterizes the identity type of `(x : A) (y : B x) → C x y`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  binary-htpy :
    (f g : (x : A) (y : B x) → C x y) → UU (l1 ⊔ l2 ⊔ l3)
  binary-htpy f g = (x : A) → f x ~ g x

  refl-binary-htpy : (f : (x : A) (y : B x) → C x y) → binary-htpy f f
  refl-binary-htpy f x = refl-htpy

  binary-htpy-eq :
    (f g : (x : A) (y : B x) → C x y) → (f ＝ g) → binary-htpy f g
  binary-htpy-eq f .f refl = refl-binary-htpy f

  is-torsorial-binary-htpy :
    (f : (x : A) (y : B x) → C x y) →
    is-torsorial (binary-htpy f)
  is-torsorial-binary-htpy f =
    is-torsorial-Eq-Π
      ( λ x g → f x ~ g)
      ( λ x → is-torsorial-htpy (f x))

  is-equiv-binary-htpy-eq :
    (f g : (x : A) (y : B x) → C x y) → is-equiv (binary-htpy-eq f g)
  is-equiv-binary-htpy-eq f =
    fundamental-theorem-id
      ( is-torsorial-binary-htpy f)
      ( binary-htpy-eq f)

  extensionality-binary-Π :
    (f g : (x : A) (y : B x) → C x y) → (f ＝ g) ≃ binary-htpy f g
  pr1 (extensionality-binary-Π f g) = binary-htpy-eq f g
  pr2 (extensionality-binary-Π f g) = is-equiv-binary-htpy-eq f g

  eq-binary-htpy :
    (f g : (x : A) (y : B x) → C x y) → binary-htpy f g → f ＝ g
  eq-binary-htpy f g = map-inv-equiv (extensionality-binary-Π f g)
```

## Properties

### Binary homotopy is equivalent to function homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  where

  binary-htpy-htpy :
    (f g : (x : A) (y : B x) → C x y) → (f ~ g) → binary-htpy f g
  binary-htpy-htpy f g =
    ind-htpy f (λ g H → binary-htpy f g) (refl-binary-htpy f)

  equiv-binary-htpy-htpy :
    (f g : (x : A) (y : B x) → C x y) → (f ~ g) ≃ binary-htpy f g
  equiv-binary-htpy-htpy f g = extensionality-binary-Π f g ∘e equiv-eq-htpy

  htpy-binary-htpy :
    (f g : (x : A) (y : B x) → C x y) → binary-htpy f g → f ~ g
  htpy-binary-htpy f g = map-inv-equiv (equiv-binary-htpy-htpy f g)

  equiv-htpy-binary-htpy :
    (f g : (x : A) (y : B x) → C x y) → binary-htpy f g ≃ (f ~ g)
  equiv-htpy-binary-htpy f g = inv-equiv (equiv-binary-htpy-htpy f g)
```
