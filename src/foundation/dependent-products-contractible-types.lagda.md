# Dependent products of contractible types

```agda
open import foundation.function-extensionality-axiom

module foundation.dependent-products-contractible-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

Given a family of [contractible types](foundation-core.contractible-types.md)
`B : A → 𝒰`, then the dependent product `Π A B` is again contractible.

## Properties

### Products of families of contractible types are contractible

```agda
abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  pr1 (is-contr-Π {A = A} {B = B} H) x = center (H x)
  pr2 (is-contr-Π {A = A} {B = B} H) f =
    eq-htpy (λ x → contraction (H x) (f x))

abstract
  is-contr-implicit-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ({x : A} → B x)
  is-contr-implicit-Π H =
    is-contr-equiv _ equiv-explicit-implicit-Π (is-contr-Π H)
```

### The type of functions into a contractible type is contractible

```agda
is-contr-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-contr B → is-contr (A → B)
is-contr-function-type is-contr-B = is-contr-Π (λ _ → is-contr-B)
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr (pair a α) (pair b β) =
    is-contr-Σ
      ( is-contr-function-type (pair b β))
      ( λ x → b)
      ( is-contr-product
        ( is-contr-Σ
          ( is-contr-function-type (pair a α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (pair b β) b)))
        ( is-contr-Σ
          ( is-contr-function-type (pair a α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (pair a α) a))))
```

### Being contractible is a proposition

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-contr-is-contr : is-contr A → is-contr (is-contr A)
    is-contr-is-contr (pair a α) =
      is-contr-Σ
        ( pair a α)
        ( a)
        ( is-contr-Π (is-prop-is-contr (pair a α) a))

  abstract
    is-property-is-contr : (H K : is-contr A) → is-contr (H ＝ K)
    is-property-is-contr H = is-prop-is-contr (is-contr-is-contr H) H
```
