# Homomorphisms of quasigroups

```agda
module group-theory.homomorphisms-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.function-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import group-theory.quasigroups
```

</details>

## Idea

A {{#concept "homomorphism of quasigroups" Agda=hom-Quasigroup}} is a map
between two quasigroups `Q, R` that preserves the multiplication. It is a
theorem that such maps then preserve the left and right division operations as
well.

## Definition

```agda
module _
  {l1 l2 : Level} (Q : Quasigroup l1) (R : Quasigroup l2)
  where

  preserves-mul-Quasigroup :
    ( type-Quasigroup Q → type-Quasigroup R) → UU (l1 ⊔ l2)
  preserves-mul-Quasigroup f =
    ( x y : type-Quasigroup Q) →
      f (mul-Quasigroup Q x y) ＝ mul-Quasigroup R (f x) (f y)

  is-prop-preserves-mul-Quasigroup :
    ( f : type-Quasigroup Q → type-Quasigroup R) →
    is-prop (preserves-mul-Quasigroup f)
  is-prop-preserves-mul-Quasigroup f =
    is-prop-Π (λ x → is-prop-Π
    ( λ y → pr2 (pr1 R) (f (pr1 (pr2 Q) x y)) (pr1 (pr2 R) (f x) (f y))))

  hom-Quasigroup : UU (l1 ⊔ l2)
  hom-Quasigroup =
    Σ (type-Quasigroup Q → type-Quasigroup R) preserves-mul-Quasigroup

  map-hom-Quasigroup : hom-Quasigroup → type-Quasigroup Q → type-Quasigroup R
  map-hom-Quasigroup f = pr1 f
```

### The identity homomorphism of quasigroups

```agda
preserves-mul-id-Quasigroup :
  {l : Level} (Q : Quasigroup l) → preserves-mul-Quasigroup Q Q id
preserves-mul-id-Quasigroup Q = λ x y → refl

id-hom-Quasigroup : {l : Level} (Q : Quasigroup l) → hom-Quasigroup Q Q
id-hom-Quasigroup Q = id , preserves-mul-id-Quasigroup Q
```

### Characterizing the identity type of homomorphisms of quasigroups

```agda
module _
  {l1 l2 : Level} (Q : Quasigroup l1) (R : Quasigroup l2)
  where

  htpy-hom-Quasigroup : (f g : hom-Quasigroup Q R) → UU (l1 ⊔ l2)
  htpy-hom-Quasigroup (f , _) (g , _) = f ~ g

  is-prop-htpy-hom-Quasigroup : (f g : hom-Quasigroup Q R) → is-prop (htpy-hom-Quasigroup f g)
  is-prop-htpy-hom-Quasigroup f g = is-prop-all-elements-equal lem
    where
    lem : all-elements-equal (htpy-hom-Quasigroup f g)
    lem p q = eq-htpy (λ x → pr1 (pr2 (pr1 R) (pr1 f x) (pr1 g x) (p x) (q x)))

  refl-htpy-hom-Quasigroup : (f : hom-Quasigroup Q R) → htpy-hom-Quasigroup f f
  refl-htpy-hom-Quasigroup f = λ x → refl

  htpy-eq-hom-Quasigroup :
    ( f g : hom-Quasigroup Q R) → f ＝ g → htpy-hom-Quasigroup f g
  htpy-eq-hom-Quasigroup f f refl = λ x → refl

  abstract
    is-torsorial-htpy-hom-Quasigroup :
      (f : hom-Quasigroup Q R) → is-torsorial (htpy-hom-Quasigroup f)
    pr1 (is-torsorial-htpy-hom-Quasigroup f) = f , refl-htpy-hom-Quasigroup f
    pr2 (is-torsorial-htpy-hom-Quasigroup (f , f-mul)) ((g , g-mul) , p) =
      eq-pair-Σ (eq-pair-Σ (eq-htpy p) (eq-is-prop (is-prop-Π
        ( λ x → is-prop-Π (λ y → is-set-Quasigroup R
        ( g (pr1 (pr2 Q) x y)) (pr1 (pr2 R) (g x) (g y)))))))
        (eq-is-prop (is-prop-htpy-hom-Quasigroup (f , f-mul) (g , g-mul)))

  abstract
    is-equiv-htpy-eq-hom-Quasigroup : (f g : hom-Quasigroup Q R) → is-equiv (htpy-eq-hom-Quasigroup f g)
    is-equiv-htpy-eq-hom-Quasigroup f = fundamental-theorem-id (is-torsorial-htpy-hom-Quasigroup f) (htpy-eq-hom-Quasigroup f)

  equiv-htpy-eq-hom-Quasigroup : (f g : hom-Quasigroup Q R) → (f ＝ g) ≃ htpy-hom-Quasigroup f g
  pr1 (equiv-htpy-eq-hom-Quasigroup f g) = htpy-eq-hom-Quasigroup f g
  pr2 (equiv-htpy-eq-hom-Quasigroup f g) = is-equiv-htpy-eq-hom-Quasigroup f g

  eq-htpy-hom-Quasigroup : {f g : hom-Quasigroup Q R} → htpy-hom-Quasigroup f g → f ＝ g
  eq-htpy-hom-Quasigroup {f} {g} = map-inv-equiv (equiv-htpy-eq-hom-Quasigroup f g)
```

## Properties

### Quasigroup homomorphisms preserve left and right division

```agda
module _
  {l1 l2 : Level} (Q : Quasigroup l1) (R : Quasigroup l2) (f : hom-Quasigroup Q R)
  where

{-
  preserves-left-div-Quasigroup :
    ( x y : type-Quasigroup Q) →
    map-hom-Quasigroup Q R f (left-div-Quasigroup Q x y) ＝
    left-div-Quasigroup R (map-hom-Quasigroup Q R f x)
      ( map-hom-Quasigroup Q R f y)
  preserves-left-div-Quasigroup x y = {!   !}

  1preserves-right-div-Quasigroup :
    ( x y : type-Quasigroup Q) →
    map-hom-Quasigroup Q R f (right-div-Quasigroup Q x y) ＝
    right-div-Quasigroup R (map-hom-Quasigroup Q R f x)
      ( map-hom-Quasigroup Q R f y)
  preserves-right-div-Quasigroup x y = {!   !}
-}
```
