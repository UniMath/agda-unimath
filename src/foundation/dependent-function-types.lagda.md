# Dependent function types

```agda
module foundation.dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans-families-of-types
open import foundation.terminal-spans-families-of-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-dependent-function-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a family `B` of types over `A`. A {{#concept "dependent function"}}
that takes elements `x : A` to elements of type `B x` is an assignment of an
element `f x : B x` for each `x : A`. In Agda, dependent functions can be
written using `λ`-abstraction, i.e., using the syntax

```text
  λ x → f x.
```

Informally, we also use the notation `x ↦ f x` for the assignment of values of a
dependent function `f`.

The type of dependent function `(x : A) → B x` is built in to the kernel of
Agda, and doesn't need to be introduced by us. The purpose of this file is to
record some properties of dependent function types.

## Definitions

### The structure of a span on a family of types on a dependent function type

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  span-type-family-Π : span-type-family (l1 ⊔ l2) B
  pr1 span-type-family-Π = (x : A) → B x
  pr2 span-type-family-Π x f = f x
```

## Properties

### Dependent function types satisfy the universal property of dependent function types

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  abstract
    universal-property-dependent-function-types-Π :
      universal-property-dependent-function-types (span-type-family-Π B)
    universal-property-dependent-function-types-Π T = is-equiv-swap-Π
```

### Dependent function types are terminal spans on families of types

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  abstract
    is-terminal-span-type-family-Π :
      is-terminal-span-type-family (span-type-family-Π B)
    is-terminal-span-type-family-Π =
      is-terminal-universal-property-dependent-function-types
        ( span-type-family-Π B)
        ( universal-property-dependent-function-types-Π B)
```

## See also

- [The globular type of dependent functions](foundation.globular-type-of-dependent-functions.md)
