# Universal property contractible types

```agda
module foundation.universal-property-contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.singleton-induction
```

</details>

## Definitions

### The dependent universal property of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  dependent-universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  dependent-universal-property-contr l a =
    (P : A → UU l) → is-equiv (ev-point a {P})
```

### The universal property of contractible types

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  universal-property-contr : (l : Level) (a : A) → UU (l1 ⊔ lsuc l)
  universal-property-contr l a =
    (X : UU l) → is-equiv (ev-point' a {X})
```

### The universal property of contractible types follows from the dependent universal property

```agda
  universal-property-dependent-universal-property-contr :
    (a : A) →
    ({l : Level} → dependent-universal-property-contr l a) →
    ({l : Level} → universal-property-contr l a)
  universal-property-dependent-universal-property-contr a dup-contr {l} X =
    dup-contr {l} (λ x → X)
```

```agda
  abstract
    is-equiv-ev-point-universal-property-contr :
      (a : A) → ({l : Level} → universal-property-contr l a) →
      is-equiv (ev-point' a {A})
    is-equiv-ev-point-universal-property-contr a up-contr =
      up-contr A

  abstract
    is-contr-is-equiv-ev-point :
      (a : A) → is-equiv (ev-point' a {A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point a H) = a
    pr2 (is-contr-is-equiv-ev-point a H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( pair (λ x → a) refl)
            ( pair id refl)))

  abstract
    is-contr-universal-property-contr :
      (a : A) →
      ({l : Level} → universal-property-contr l a) → is-contr A
    is-contr-universal-property-contr a up-contr =
      is-contr-is-equiv-ev-point a
        ( is-equiv-ev-point-universal-property-contr a up-contr)

  abstract
    is-contr-dependent-universal-property-contr :
      (a : A) →
      ({l : Level} → dependent-universal-property-contr l a) → is-contr A
    is-contr-dependent-universal-property-contr a dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)

  abstract
    dependent-universal-property-contr-is-contr :
      (a : A) → is-contr A →
      {l : Level} → dependent-universal-property-contr l a
    dependent-universal-property-contr-is-contr a H {l} P =
      is-equiv-is-invertible
        ( ind-singleton a H P)
        ( compute-ind-singleton a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton a H
              ( λ x → ind-singleton a H P (f a) x ＝ f x)
              ( compute-ind-singleton a H P (f a))))

  equiv-dependent-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (B : A → UU l) → ((x : A) → B x) ≃ B a
  pr1 (equiv-dependent-universal-property-contr a H P) = ev-point a
  pr2 (equiv-dependent-universal-property-contr a H P) =
    dependent-universal-property-contr-is-contr a H P

  apply-dependent-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (B : A → UU l) → (B a → ((x : A) → B x))
  apply-dependent-universal-property-contr a H P =
    map-inv-equiv (equiv-dependent-universal-property-contr a H P)

  abstract
    universal-property-contr-is-contr :
      (a : A) → is-contr A → {l : Level} → universal-property-contr l a
    universal-property-contr-is-contr a H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr a H X) = ev-point' a
  pr2 (equiv-universal-property-contr a H X) =
    universal-property-contr-is-contr a H X

  apply-universal-property-contr :
    (a : A) → is-contr A → {l : Level} (X : UU l) → X → (A → X)
  apply-universal-property-contr a H X =
    map-inv-equiv (equiv-universal-property-contr a H X)
```

## See also

- [Singleton induction](foundation-core.singleton-induction.md)
