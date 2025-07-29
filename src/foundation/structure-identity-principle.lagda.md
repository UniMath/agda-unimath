# The structure identity principle

```agda
module foundation.structure-identity-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

[Structure](foundation.structure.md) is presented in type theory by
[dependent pair types](foundation.dependent-pair-types.md). The
{{#concept "structure identity principle" Disambiguation="for types" Agda=structure-identity-principle}}
is a way to characterize the [identity type](foundation-core.identity-types.md)
of a structure, using characterizations of the identity types of its components.

## Lemma

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  { D : (x : A) → B x → C x → UU l4}
  where

  abstract
    is-torsorial-Eq-structure :
      (is-torsorial-AC : is-torsorial C) (t : Σ A C) →
      is-torsorial (λ y → D (pr1 t) y (pr2 t)) →
      is-torsorial (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
    is-torsorial-Eq-structure is-torsorial-AC t is-torsorial-BD =
      is-contr-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
        ( interchange-Σ-Σ D)
        ( is-contr-Σ is-torsorial-AC t is-torsorial-BD)
```

## Theorem

### The structure identity principle

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {Eq-A : A → UU l3}
  (Eq-B : {x : A} → B x → Eq-A x → UU l4)
  {a : A} {b : B a} (refl-A : Eq-A a) (refl-B : Eq-B b refl-A)
  where

  abstract
    structure-identity-principle :
      {f : (x : A) → a ＝ x → Eq-A x}
      {g : (y : B a) → b ＝ y → Eq-B y refl-A} →
      (h : (z : Σ A B) → (pair a b) ＝ z → Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))) →
      ((x : A) → is-equiv (f x)) → ((y : B a) → is-equiv (g y)) →
      (z : Σ A B) → is-equiv (h z)
    structure-identity-principle {f} {g} h H K =
      fundamental-theorem-id
        ( is-torsorial-Eq-structure
          ( fundamental-theorem-id' f H)
          ( pair a refl-A)
          ( fundamental-theorem-id' g K))
        ( h)

  map-extensionality-Σ :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x)
    (g : (y : B a) → (b ＝ y) ≃ Eq-B y refl-A) →
    (z : Σ A B) → pair a b ＝ z → Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))
  pr1 (map-extensionality-Σ f g .(pair a b) refl) = refl-A
  pr2 (map-extensionality-Σ f g .(pair a b) refl) = refl-B

  extensionality-Σ :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x)
    (g : (y : B a) → (b ＝ y) ≃ Eq-B y refl-A) →
    (z : Σ A B) → (pair a b ＝ z) ≃ Σ (Eq-A (pr1 z)) (Eq-B (pr2 z))
  pr1 (extensionality-Σ f g z) = map-extensionality-Σ f g z
  pr2 (extensionality-Σ f g z) =
    structure-identity-principle
      ( map-extensionality-Σ f g)
      ( λ x → is-equiv-map-equiv (f x))
      ( λ y → is-equiv-map-equiv (g y))
      ( z)

  inv-map-extensionality-Σ :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x)
    (g : (y : B a) → (b ＝ y) ≃ Eq-B y refl-A) →
    (z : Σ A B) → Σ (Eq-A (pr1 z)) (Eq-B (pr2 z)) → pair a b ＝ z
  inv-map-extensionality-Σ f g z = map-inv-equiv (extensionality-Σ f g z)
```

## External links

- [Structure Identity Principle](https://1lab.dev/1Lab.Univalence.SIP.html) at
  1lab
- [structure identity principle](https://ncatlab.org/nlab/show/structure+identity+principle)
  at $n$Lab
