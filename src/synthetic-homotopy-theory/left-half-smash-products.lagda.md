# Left half-smash products

```agda
module synthetic-homotopy-theory.left-half-smash-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.cofibers-of-maps
```

</details>

## Idea

Given a type `A` and a [pointed type](structured-types.pointed-types.md) `b : B`
we may form the
{{#concept "left half-smash product" Disambiguation="of a type and a pointed type" Agda=pointed-type-left-half-smash}}
`A ⋉∗ B` as the [cofiber](synthetic-homotopy-theory.cofibers-of-maps.md) of the
canonical inclusion `A → A × B` at the base point of `B`. In other words, the
left half-smash product is the [pushout](synthetic-homotopy-theory.pushouts.md)

```text
    A  -----> A × B
    |           |
    |           |
    ∨         ⌜ ∨
    * ------> A ⋉∗ B.
```

## Definitions

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : Pointed-Type l2)
  where

  map-left-half-smash : A → A × type-Pointed-Type B
  map-left-half-smash a = (a , point-Pointed-Type B)

  type-left-half-smash : UU (l1 ⊔ l2)
  type-left-half-smash =
    cofiber map-left-half-smash

  point-left-half-smash : type-left-half-smash
  point-left-half-smash =
    point-cofiber map-left-half-smash

  pointed-type-left-half-smash : Pointed-Type (l1 ⊔ l2)
  pointed-type-left-half-smash =
    pointed-type-cofiber map-left-half-smash

  infixr 15 _⋉∗_
  _⋉∗_ : Pointed-Type (l1 ⊔ l2)
  _⋉∗_ = pointed-type-left-half-smash
```

> **Notation.** The symbols used for the left half-smash product `_⋉∗_` are the
> [left normal factor semidirect product](https://codepoints.net/U+22c9) `⋉`
> (agda-input: `\ltimes` `\join`), and the
> [asterisk operator](https://codepoints.net/U+2217) `∗` (agda-input: `\ast`),
> not the [asterisk](https://codepoints.net/U+002A) `*`.

## Properties

### The left half-smash product is a left tensoring

Given a type `A` and a pointed type `B`, then we have adjunctions

$$
  (A ⋉_* -) ⊣ (A → -) \quad\text{and}\quad (- ⋉_* B) ⊣ (B →_* -)
$$

viewed as functors into pointed types. In other words, we have equivalences

$$
  (A ⋉_* B →_* C) ≃ (B →_* (A → C)) \quad\text{and}\quad (A ⋉_* B →_* C) ≃ (A → (B →_* C))
$$

for every pointed type `C`.

This is Remark 3.2 of {{#cite Lavenir23}}.

**Proof.** This is a consequence of the pullback-property of pushouts.

> This remains to be formalized.

## References

{{#bibliography}}

## See also

- [Smash products of pointed types](synthetic-homotopy-theory.smash-products-of-pointed-types.md)
