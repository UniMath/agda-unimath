# Implicit function types

```agda
module foundation.implicit-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Properties

### Dependent function types taking implicit arguments are equivalent to dependent function types taking explicit arguments

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  implicit-explicit-Π : ((x : A) → B x) → {x : A} → B x
  implicit-explicit-Π f {x} = f x

  explicit-implicit-Π : ({x : A} → B x) → (x : A) → B x
  explicit-implicit-Π f x = f {x}

  is-equiv-implicit-explicit-Π : is-equiv implicit-explicit-Π
  pr1 (pr1 is-equiv-implicit-explicit-Π) = explicit-implicit-Π
  pr2 (pr1 is-equiv-implicit-explicit-Π) = refl-htpy
  pr1 (pr2 is-equiv-implicit-explicit-Π) = explicit-implicit-Π
  pr2 (pr2 is-equiv-implicit-explicit-Π) = refl-htpy

  is-equiv-explicit-implicit-Π : is-equiv explicit-implicit-Π
  pr1 (pr1 is-equiv-explicit-implicit-Π) = implicit-explicit-Π
  pr2 (pr1 is-equiv-explicit-implicit-Π) = refl-htpy
  pr1 (pr2 is-equiv-explicit-implicit-Π) = implicit-explicit-Π
  pr2 (pr2 is-equiv-explicit-implicit-Π) = refl-htpy

  equiv-implicit-explicit-Π : ((x : A) → B x) ≃ ({x : A} → B x)
  pr1 equiv-implicit-explicit-Π = implicit-explicit-Π
  pr2 equiv-implicit-explicit-Π = is-equiv-implicit-explicit-Π

  equiv-explicit-implicit-Π : ({x : A} → B x) ≃ ((x : A) → B x)
  pr1 equiv-explicit-implicit-Π = explicit-implicit-Π
  pr2 equiv-explicit-implicit-Π = is-equiv-explicit-implicit-Π
```

### Equality of explicit functions is equality of implicit functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x}
  where

  equiv-eq-implicit-eq-explicit-Π : (f ＝ g) ≃ (Id (λ {x} → f x) (λ {x} → g x))
  equiv-eq-implicit-eq-explicit-Π = equiv-ap equiv-implicit-explicit-Π f g

  eq-implicit-eq-explicit-Π : (f ＝ g) → (Id (λ {x} → f x) (λ {x} → g x))
  eq-implicit-eq-explicit-Π = map-equiv equiv-eq-implicit-eq-explicit-Π

  equiv-eq-explicit-eq-implicit-Π : (Id (λ {x} → f x) (λ {x} → g x)) ≃ (f ＝ g)
  equiv-eq-explicit-eq-implicit-Π =
    equiv-ap equiv-explicit-implicit-Π (λ {x} → f x) (λ {x} → g x)

  eq-explicit-eq-implicit-Π : (Id (λ {x} → f x) (λ {x} → g x)) → (f ＝ g)
  eq-explicit-eq-implicit-Π = map-equiv equiv-eq-explicit-eq-implicit-Π
```

## See also

- Function extensionality for implicit function types is established in
  [`foundation.function-extensionality`](foundation.function-extensionality.md).
