# Type arithmetic with dependent function types

```agda
module foundation.type-arithmetic-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.universe-levels
```

</details>

## Properties

### The swap function `((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  swap-Π : ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
  swap-Π f y x = f x y

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  is-equiv-swap-Π : is-equiv (swap-Π {C = C})
  is-equiv-swap-Π = is-equiv-has-inverse swap-Π refl-htpy refl-htpy

  equiv-swap-Π : ((x : A) (y : B) → C x y) ≃ ((y : B) (x : A) → C x y)
  pr1 equiv-swap-Π = swap-Π
  pr2 equiv-swap-Π = is-equiv-swap-Π
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).

- Arithmetical laws involving cartesian product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).

- In [`foundation.universal-property-empty-type`](foundation.universal-property-empty-type.md)
  we show that `empty` is the initial type, which can be considered a
  *left zero law for function types* (`(empty → A) ≃ unit`).
- That `unit` is the terminal type is a corollary of `is-contr-Π`, which may be found in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).
  This can be considered a *right zero law for function types* (`(A → unit) ≃ unit`).
