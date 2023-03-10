# Identity types

```agda
module foundation.identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.identity-types public

open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
```

</details>

## Idea

The equality relation on a type is a reflexive relation, with the universal property that it maps uniquely into any other reflexive relation. In type theory, we introduce the identity type as an inductive family of types, where the induction principle can be understood as expressing that the identity type is the least reflexive relation.

## Properties

### The groupoidal operations on identity types are equivalences

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : x ＝ y) → inv p)
    is-equiv-inv x y = is-equiv-has-inverse inv inv-inv inv-inv

  equiv-inv : (x y : A) → (x ＝ y) ≃ (y ＝ x)
  pr1 (equiv-inv x y) = inv
  pr2 (equiv-inv x y) = is-equiv-inv x y

  inv-concat : {x y : A} (p : x ＝ y) (z : A) → x ＝ z → y ＝ z
  inv-concat p = concat (inv p)

  isretr-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (inv-concat p z ∘ concat p z) ~ id
  isretr-inv-concat refl z q = refl

  issec-inv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (concat p z ∘ inv-concat p z) ~ id
  issec-inv-concat refl z refl = refl

  abstract
    is-equiv-concat :
      {x y : A} (p : x ＝ y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z =
      is-equiv-has-inverse
        ( inv-concat p z)
        ( issec-inv-concat p z)
        ( isretr-inv-concat p z)

  equiv-concat :
    {x y : A} (p : x ＝ y) (z : A) → (y ＝ z) ≃ (x ＝ z)
  pr1 (equiv-concat p z) = concat p z
  pr2 (equiv-concat p z) = is-equiv-concat p z

  equiv-concat-equiv :
    {x x' : A} → ((y : A) → (x ＝ y) ≃ (x' ＝ y)) ≃ (x' ＝ x)
  pr1 (equiv-concat-equiv {x}) e = map-equiv (e x) refl
  pr2 equiv-concat-equiv =
    is-equiv-has-inverse
      equiv-concat
      (λ { refl → refl })
      (λ e → eq-htpy (λ y → eq-htpy-equiv (λ { refl → right-unit })))

  inv-concat' : (x : A) {y z : A} → y ＝ z → x ＝ z → x ＝ y
  inv-concat' x q = concat' x (inv q)

  isretr-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (inv-concat' x q ∘ concat' x q) ~ id
  isretr-inv-concat' x refl refl = refl

  issec-inv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (concat' x q ∘ inv-concat' x q) ~ id
  issec-inv-concat' x refl refl = refl

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : y ＝ z) → is-equiv (concat' x q)
    is-equiv-concat' x q =
      is-equiv-has-inverse
        ( inv-concat' x q)
        ( issec-inv-concat' x q)
        ( isretr-inv-concat' x q)

  equiv-concat' :
    (x : A) {y z : A} (q : y ＝ z) → (x ＝ y) ≃ (x ＝ z)
  pr1 (equiv-concat' x q) = concat' x q
  pr2 (equiv-concat' x q) = is-equiv-concat' x q

is-binary-equiv-concat :
  {l : Level} {A : UU l} {x y z : A} →
  is-binary-equiv (λ (p : x ＝ y) (q : y ＝ z) → p ∙ q)
is-binary-equiv-concat {l} {A} {x} {y} {z} =
  pair (λ q → is-equiv-concat' x q) (λ p → is-equiv-concat p z)

convert-eq-values :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → (f x ＝ f y) ≃ (g x ＝ g y)
convert-eq-values {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))
```

## Transposing inverses is an equivalence

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  abstract
    is-equiv-inv-con :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) → is-equiv (inv-con p q r)
    is-equiv-inv-con refl q r = is-equiv-id

  equiv-inv-con :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    ((p ∙ q) ＝ r) ≃ (q ＝ ((inv p) ∙ r))
  pr1 (equiv-inv-con p q r) = inv-con p q r
  pr2 (equiv-inv-con p q r) = is-equiv-inv-con p q r

  abstract
    is-equiv-con-inv :
      (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) → is-equiv (con-inv p q r)
    is-equiv-con-inv p refl r =
      is-equiv-comp
        ( concat' p (inv right-unit))
        ( concat (inv right-unit) r)
        ( is-equiv-concat (inv right-unit) r)
        ( is-equiv-concat' p (inv right-unit))

  equiv-con-inv :
    (p : x ＝ y) (q : y ＝ z) (r : x ＝ z) →
    ((p ∙ q) ＝ r) ≃ (p ＝ (r ∙ (inv q)))
  pr1 (equiv-con-inv p q r) = con-inv p q r
  pr2 (equiv-con-inv p q r) = is-equiv-con-inv p q r
```

### Transport is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  inv-tr : x ＝ y → B y → B x
  inv-tr p = tr B (inv p)

  isretr-inv-tr : (p : x ＝ y) → ((inv-tr p ) ∘ (tr B p)) ~ id
  isretr-inv-tr refl b = refl

  issec-inv-tr : (p : x ＝ y) → ((tr B p) ∘ (inv-tr p)) ~ id
  issec-inv-tr refl b = refl

  abstract
    is-equiv-tr : (p : x ＝ y) → is-equiv (tr B p)
    is-equiv-tr p =
      is-equiv-has-inverse
        ( inv-tr p)
        ( issec-inv-tr p)
        ( isretr-inv-tr p)

  equiv-tr : x ＝ y → (B x) ≃ (B y)
  pr1 (equiv-tr p) = tr B p
  pr2 (equiv-tr p) = is-equiv-tr p
```
