# The structure identity principle

```agda
module foundation.structure-identity-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universe-levels
```

</details>

## Idea

Structure is presented in type theory by dependent pair types. The structure identity principle is a way to characterize the identity type of a structure, using characterizations of the identity types of its components.

## Lemma

```agda
module _
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where

  abstract
    is-contr-total-Eq-structure :
      (is-contr-AC : is-contr (Σ A C)) (t : Σ A C) →
      is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
      is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
    is-contr-total-Eq-structure is-contr-AC t is-contr-BD =
      is-contr-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
        ( interchange-Σ-Σ D)
        ( is-contr-Σ is-contr-AC t is-contr-BD)
```

## Theorem

### The structure identity principle

```agda
module _
  {l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {Eq-A : A → UU l3}
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
        ( is-contr-total-Eq-structure
          ( λ x → Eq-B)
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
```
