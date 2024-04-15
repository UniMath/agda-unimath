# Counting the elements of dependent function types

```agda
module univalent-combinatorics.dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Dependent products of finite types indexed by a finite type are finite.

## Properties

### Counting dependent products indexed by standard finite types

If the elements of `A` can be counted and if for each `x : A` the elements of
`B x` can be counted, then the elements of `Π A B` can be counted.

```agda
count-Π-Fin :
  {l1 : Level} (k : ℕ) {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} zero-ℕ {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} (succ-ℕ k) {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coproduct B)
    ( count-product
      ( count-Π-Fin k (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( e (inr star))))
```

### Counting on dependent function types

```agda
count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (number-of-elements-count e) (λ x → f (map-equiv-count e x)))
```

### Finiteness of dependent function types

```agda
abstract
  is-finite-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
  is-finite-Π {l1} {l2} {A} {B} f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop ((x : A) → B x))
      ( λ e →
        apply-universal-property-trunc-Prop
          ( finite-choice f g)
          ( is-finite-Prop ((x : A) → B x))
          ( λ h → unit-trunc-Prop (count-Π e h)))

  is-finite-Π' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((x : A) → is-finite (B x)) → is-finite ({x : A} → B x)
  is-finite-Π' {l1} {l2} {A} {B} f g =
    is-finite-equiv
      (( pair
        ( λ f {x} → f x)
        ( is-equiv-is-invertible
          ( λ g x → g {x})
          ( refl-htpy)
          ( refl-htpy))))
      (is-finite-Π f g)

Π-𝔽 : {l1 l2 : Level} (A : 𝔽 l1) (B : type-𝔽 A → 𝔽 l2) → 𝔽 (l1 ⊔ l2)
pr1 (Π-𝔽 A B) = (x : type-𝔽 A) → type-𝔽 (B x)
pr2 (Π-𝔽 A B) = is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x))

Π-𝔽' : {l1 l2 : Level} (A : 𝔽 l1) (B : type-𝔽 A → 𝔽 l2) → 𝔽 (l1 ⊔ l2)
pr1 (Π-𝔽' A B) = {x : type-𝔽 A} → type-𝔽 (B x)
pr2 (Π-𝔽' A B) =
  is-finite-Π' (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x))
```
