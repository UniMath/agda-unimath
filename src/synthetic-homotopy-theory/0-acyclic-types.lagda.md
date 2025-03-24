# `0`-acyclic types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module synthetic-homotopy-theory.0-acyclic-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.dependent-products-propositions funext
open import foundation.functoriality-propositional-truncation funext univalence truncations
open import foundation.inhabited-types funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.propositions funext univalence
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-maps funext univalence truncations
open import synthetic-homotopy-theory.truncated-acyclic-maps funext univalence truncations
open import synthetic-homotopy-theory.truncated-acyclic-types funext univalence truncations
```

</details>

## Idea

A type is **`0`-acyclic** if its
[suspension](synthetic-homotopy-theory.suspensions-of-types.md) is
[`0`-connected](foundation.0-connected-types.md).

We can characterize the `0`-acyclic types as the
[inhabited types](foundation.inhabited-types.md).

## Definition

### The predicate of being a `0`-acyclic type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-0-acyclic-Prop : Prop l
  is-0-acyclic-Prop = is-truncated-acyclic-Prop zero-𝕋 A

  is-0-acyclic : UU l
  is-0-acyclic = type-Prop is-0-acyclic-Prop

  is-prop-is-0-acyclic : is-prop is-0-acyclic
  is-prop-is-0-acyclic = is-prop-type-Prop is-0-acyclic-Prop
```

## Properties

### A type is `0`-acyclic if and only if it is inhabited

```agda
module _
  {l : Level} {A : UU l}
  where

  is-inhabited-is-0-acyclic : is-0-acyclic A → is-inhabited A
  is-inhabited-is-0-acyclic ac =
    map-trunc-Prop
      ( pr1)
      ( is-surjective-is-0-acyclic-map
        ( terminal-map A)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( star))

  is-0-acyclic-is-inhabited : is-inhabited A → is-0-acyclic A
  is-0-acyclic-is-inhabited h =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-0-acyclic-map-is-surjective
        ( terminal-map A)
        ( λ u →
          map-trunc-Prop
            (λ a → (a , (contraction is-contr-unit u)))
            ( h)))
```

## See also

- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
