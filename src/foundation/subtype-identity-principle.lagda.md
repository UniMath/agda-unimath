# The subtype identity principle

```agda
module foundation.subtype-identity-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The **subtype identity principle** allows us to efficiently characterize the
[identity type](foundation-core.identity-types.md) of a
[subtype](foundation-core.subtypes.md), using a characterization of the identity
type of the base type.

## Lemma

The following is a general construction that will help us show that the identity
type of a subtype agrees with the identity type of the original type. We already
know that the first projection of a family of
[propositions](foundation-core.propositions.md) is an
[embedding](foundation-core.embeddings.md), but the following lemma still has
its uses.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-torsorial-Eq-subtype :
      {l3 : Level} {P : A → UU l3} →
      is-torsorial B → ((x : A) → is-prop (P x)) →
      (a : A) (b : B a) (p : P a) →
      is-torsorial (λ (t : Σ A P) → B (pr1 t))
    is-torsorial-Eq-subtype {P = P} is-torsorial-B is-subtype-P a b p =
      is-contr-equiv
        ( Σ (Σ A B) (P ∘ pr1))
        ( equiv-right-swap-Σ)
        ( is-contr-equiv
          ( P a)
          ( left-unit-law-Σ-is-contr is-torsorial-B (a , b))
          ( is-proof-irrelevant-is-prop (is-subtype-P a) p))
```

## Theorem

### The subtype identity principle

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2}
  (is-prop-P : (x : A) → is-prop (P x)) {Eq-A : A → UU l3}
  {a : A} (p : P a) (refl-A : Eq-A a)
  where

  abstract
    subtype-identity-principle :
      {f : (x : A) → a ＝ x → Eq-A x}
      (h : (z : (Σ A P)) → (a , p) ＝ z → Eq-A (pr1 z)) →
      ((x : A) → is-equiv (f x)) → (z : Σ A P) → is-equiv (h z)
    subtype-identity-principle {f} h H =
      fundamental-theorem-id
        ( is-torsorial-Eq-subtype
          ( fundamental-theorem-id' f H)
          ( is-prop-P)
          ( a)
          ( refl-A)
          ( p))
        ( h)

module _
  {l1 l2 l3 : Level} {A : UU l1} (P : A → Prop l2) {Eq-A : A → UU l3}
  {a : A} (p : type-Prop (P a)) (refl-A : Eq-A a)
  where

  map-extensionality-type-subtype :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x) →
    (z : Σ A (type-Prop ∘ P)) → (a , p) ＝ z → Eq-A (pr1 z)
  map-extensionality-type-subtype f .(a , p) refl = refl-A

  extensionality-type-subtype :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x) →
    (z : Σ A (type-Prop ∘ P)) → ((a , p) ＝ z) ≃ Eq-A (pr1 z)
  pr1 (extensionality-type-subtype f z) = map-extensionality-type-subtype f z
  pr2 (extensionality-type-subtype f z) =
    subtype-identity-principle
      ( is-prop-type-Prop ∘ P)
      ( p)
      ( refl-A)
      ( map-extensionality-type-subtype f)
      ( is-equiv-map-equiv ∘ f)
      ( z)

  map-inv-extensionality-type-subtype :
    (f : (x : A) → (a ＝ x) ≃ Eq-A x) →
    (z : Σ A (type-Prop ∘ P)) → Eq-A (pr1 z) → (a , p) ＝ z
  map-inv-extensionality-type-subtype f z =
    map-inv-equiv (extensionality-type-subtype f z)
```
