# Counting the elements of dependent function types

```agda
module univalent-combinatorics.dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
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
count-Π-Fin {l1} zero-ℕ {B} c =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} (succ-ℕ k) {B} c =
  count-equiv'
    ( equiv-dependent-universal-property-coproduct B)
    ( count-product
      ( count-Π-Fin k (λ i → c (inl-Fin k i)))
      ( count-equiv'
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( c (inr star))))

number-of-elements-count-Π-Fin :
  {l1 : Level} (k : ℕ) {B : Fin k → UU l1} →
  (c : (x : Fin k) → count (B x)) →
  number-of-elements-count (count-Π-Fin k c) ＝
  Π-ℕ k (λ i → number-of-elements-count (c i))
number-of-elements-count-Π-Fin zero-ℕ c = refl
number-of-elements-count-Π-Fin (succ-ℕ k) c =
  ( number-of-elements-count-product
    ( count-Π-Fin k (λ i → c (inl-Fin k i)))
    ( c (inr star))) ∙
  ( ap
    ( _*ℕ number-of-elements-count (c (inr star)))
    ( number-of-elements-count-Π-Fin k (λ i → c (inl-Fin k i))))
```

### Counting on dependent function types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (c : count A) (d : (x : A) → count (B x))
  where

  count-Π : count ((x : A) → B x)
  count-Π =
    count-equiv'
      ( equiv-precomp-Π (equiv-count c) B)
      ( count-Π-Fin
        ( number-of-elements-count c)
        ( λ i → d (map-equiv-count c i)))

  number-of-elements-count-Π :
    number-of-elements-count count-Π ＝
    Π-ℕ
      ( number-of-elements-count c)
      ( λ i →
        number-of-elements-count (d (map-equiv-count c i)))
  number-of-elements-count-Π =
    number-of-elements-count-Π-Fin
      ( number-of-elements-count c)
      ( λ i → d (map-equiv-count c i))
```

### Finiteness of dependent function types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-finite-Π :
      is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
    is-finite-Π f g =
      apply-universal-property-trunc-Prop f
        ( is-finite-Prop ((x : A) → B x))
        ( λ e →
          apply-universal-property-trunc-Prop
            ( finite-choice f g)
            ( is-finite-Prop ((x : A) → B x))
            ( λ h → unit-trunc-Prop (count-Π e h)))

    is-finite-Π' :
      is-finite A → ((x : A) → is-finite (B x)) → is-finite ({x : A} → B x)
    is-finite-Π' f g =
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
