# Dependent products of contractible types

```agda
module foundation.dependent-products-contractible-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
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
  pr1 (is-contr-implicit-Π H) = center (H _)
  pr2 (is-contr-implicit-Π H) f =
    ap implicit-explicit-Π (eq-htpy (λ x → contraction (H x) f))
```

### The type of functions into a contractible type is contractible

```agda
is-contr-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-contr B → is-contr (A → B)
is-contr-function-type is-contr-B = is-contr-Π (λ _ → is-contr-B)
```
