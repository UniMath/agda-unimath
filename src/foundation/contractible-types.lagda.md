# Contractible types

```agda
module foundation.contractible-types where

open import foundation-core.contractible-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences-contractible-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.logical-equivalences
open import foundation.raising-universe-levels-unit-type
open import foundation.subuniverse-of-contractible-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Contractible types are `k`-truncated for any `k`

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-contr : (k : 𝕋) → is-contr A → is-trunc k A
    is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
    is-trunc-is-contr (succ-𝕋 k) is-contr-A =
      is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)
```

### Contractibility of Σ-types where the dependent type is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  is-contr-Σ-is-prop :
    ((x : A) → is-prop (B x)) → ((x : A) → B x → a ＝ x) → is-contr (Σ A B)
  pr1 (is-contr-Σ-is-prop p f) = a , b
  pr2 (is-contr-Σ-is-prop p f) (x , y) =
    eq-type-subtype (λ x' → B x' , p x') (f x y)
```

### The diagonal of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-equiv (diagonal-exponential A A)
    is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H = H A

  abstract
    is-contr-is-equiv-self-diagonal-exponential :
      is-equiv (diagonal-exponential A A) → is-contr A
    is-contr-is-equiv-self-diagonal-exponential H =
      tot (λ x → htpy-eq) (center (is-contr-map-is-equiv H id))

  abstract
    is-contr-is-equiv-diagonal-exponential :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential H =
      is-contr-is-equiv-self-diagonal-exponential
        ( is-equiv-self-diagonal-exponential-is-equiv-diagonal-exponential H)

  abstract
    is-equiv-diagonal-exponential-is-contr :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential X A)
    is-equiv-diagonal-exponential-is-contr H X =
      is-equiv-is-invertible
        ( ev-point' (center H))
        ( λ f → eq-htpy (λ x → ap f (contraction H x)))
        ( refl-htpy)

  equiv-diagonal-exponential-is-contr :
    {l : Level} (X : UU l) → is-contr A → X ≃ (A → X)
  pr1 (equiv-diagonal-exponential-is-contr X H) =
    diagonal-exponential X A
  pr2 (equiv-diagonal-exponential-is-contr X H) =
    is-equiv-diagonal-exponential-is-contr H X

  abstract
    is-equiv-diagonal-exponential-is-contr' :
      is-contr A →
      {l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)
    is-equiv-diagonal-exponential-is-contr' H X =
      is-equiv-is-invertible
        ( λ _ → center H)
        ( λ x → eq-htpy (contraction H ∘ x))
        ( contraction H)

  equiv-diagonal-exponential-is-contr' :
    {l : Level} (X : UU l) → is-contr A → A ≃ (X → A)
  equiv-diagonal-exponential-is-contr' X H =
    ( diagonal-exponential A X , is-equiv-diagonal-exponential-is-contr' H X)

  abstract
    is-contr-is-equiv-diagonal-exponential' :
      ({l : Level} (X : UU l) → is-equiv (diagonal-exponential A X)) →
      is-contr A
    is-contr-is-equiv-diagonal-exponential' H =
      is-contr-is-equiv-self-diagonal-exponential (H A)
```

## See also

- [Dependent products of contractible types](foundation.dependent-products-contractible-types.md)
- [Equivalences of contractible types](foundation.equivalences-contractible-types.md)
- [The subuniverse of contractible types](foundation.subuniverse-of-contractible-types.md)
