# The Whitehead principle for types

```agda
module synthetic-homotopy-theory.whitehead-principle-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.infinity-connected-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "Whitehead principle" Agda=Whitehead-Principle}} asserts that
[∞-connected types](foundation.infinity-connected-types.md) are
[contractible](foundation-core.contractible-types.md). I.e., if a type is
$n$-[connected](foundation.connected-types.md) for every $n$, then it is
contractible. This principle is also referred to as _hypercompleteness_ and is
not validated in every ∞-topos.

In
(`whitehead-principle-maps`)[synthetic-homotopy-theory.whitehead-principle-maps.md]
we show, assuming Whitehead principles in enough universes, that the Whitehead
principle for types is equivalent to asking that maps whose fibers are
∞-connected are equivalences.

## Definition

```agda
Whitehead-Principle-Level : (l : Level) → UU (lsuc l)
Whitehead-Principle-Level l = (X : UU l) → is-∞-connected X → is-contr X

Whitehead-Principle : UUω
Whitehead-Principle = {l : Level} → Whitehead-Principle-Level l
```

## See also

- [The plus principle](synthetic-homotopy-theory.plus-principle.md)

## External links

- [Wikipedia page on the Whitehead theorem](https://en.m.wikipedia.org/w/index.php?title=Whitehead_theorem&oldid=1278836995)
- [nlab article on hypercomplete objects in an ∞-topos](https://ncatlab.org/nlab/show/hypercomplete+object)

## References

For the equivalent concept in the ∞-categorical semantics of homotopy type
theory, cf. §6.5.2 of Lurie's _Higher Topos Theory_ {{#cite Lurie09}}.

{{#bibliography}}
