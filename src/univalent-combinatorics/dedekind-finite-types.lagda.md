# Dedekind finite types

```agda
module univalent-combinatorics.dedekind-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Dedekind finite types" Agda=Dedekind-Finite-Type Agda=is-dedekind-finite}}
are types `X` with the [property](foundation-core.propositions.md) that every
self-[embedding](foundation-core.embeddings.md) `X ↪ X` is an
[equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being a Dedekind finite type

```agda
is-dedekind-finite-Prop : {l : Level} → UU l → Prop l
is-dedekind-finite-Prop X =
  Π-Prop
    ( X → X)
    ( λ f → function-Prop (is-emb f) (is-equiv-Prop f))

is-dedekind-finite : {l : Level} → UU l → UU l
is-dedekind-finite X = type-Prop (is-dedekind-finite-Prop X)
```

### The subuniverse of Dedekind finite types

```agda
Dedekind-Finite-Type : (l : Level) → UU (lsuc l)
Dedekind-Finite-Type l = Σ (UU l) is-dedekind-finite

module _
  {l : Level} (X : Dedekind-Finite-Type l)
  where

  type-Dedekind-Finite-Type : UU l
  type-Dedekind-Finite-Type = pr1 X

  is-dedekind-finite-Dedekind-Finite-Type :
    is-dedekind-finite type-Dedekind-Finite-Type
  is-dedekind-finite-Dedekind-Finite-Type = pr2 X
```

## Properties

### If two Dedekind finite types mutually embed, they are equivalent

This can be understood as a constructive
[Cantor–Schröder–Bernstein theorem](foundation.cantor-schroder-bernstein-escardo.md)
for Dedekind finite types.

**Proof.** Given embeddings `f : X ↪ Y` and `g : Y ↪ X`, we have a commuting
diagram

```text
       g ∘ f
    X ------> X
    |       ∧ |
  f |   g /   | f
    |   /     |
    ∨ /       ∨
    Y ------> Y.
       f ∘ g
```

The top and bottom rows are equivalences by Dedekind finiteness, so by the
6-for-2 property of equivalences every edge in this diagram is an equivalence. ∎

```agda
module _
  {l1 l2 : Level}
  (X : Dedekind-Finite-Type l1) (Y : Dedekind-Finite-Type l2)
  (f : type-Dedekind-Finite-Type X ↪ type-Dedekind-Finite-Type Y)
  (g : type-Dedekind-Finite-Type Y ↪ type-Dedekind-Finite-Type X)
  where

  is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type :
    is-equiv (map-emb f)
  is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type =
    is-equiv-left-is-equiv-top-is-equiv-bottom-square
      ( map-emb f)
      ( map-emb f)
      ( map-emb g)
      ( refl-htpy)
      ( refl-htpy)
      ( is-dedekind-finite-Dedekind-Finite-Type X
        ( map-emb g ∘ map-emb f)
        ( is-emb-map-comp-emb g f))
      ( is-dedekind-finite-Dedekind-Finite-Type Y
        ( map-emb f ∘ map-emb g)
        ( is-emb-map-comp-emb f g))

  Cantor-Schröder-Bernstein-Dedekind-Finite-Type :
    type-Dedekind-Finite-Type X ≃ type-Dedekind-Finite-Type Y
  Cantor-Schröder-Bernstein-Dedekind-Finite-Type =
    ( map-emb f , is-equiv-map-Cantor-Schröder-Bernstein-Dedekind-Finite-Type)
```

### If all elements are merely equal, then the type is Dedekind finite

```agda
is-dedekind-finite-all-elements-merely-equal :
  {l : Level} {X : UU l} → ((x y : X) → ║ x ＝ y ║₋₁) → is-dedekind-finite X
is-dedekind-finite-all-elements-merely-equal H f =
  is-equiv-is-emb-is-surjective (λ x → map-trunc-Prop (x ,_) (H (f x) x))
```

### Propositions are Dedekind finite

```agda
is-dedekind-finite-is-prop :
  {l : Level} {X : UU l} → is-prop X → is-dedekind-finite X
is-dedekind-finite-is-prop H f is-emb-f =
  is-equiv-is-split-surjective-is-injective f
    ( is-injective-is-emb is-emb-f)
    ( λ x → (x , eq-is-prop H))
```

## Comments

It seems to be an open problem whether Dedekind finite types are closed under
coproducts or products. {{#cite Sto87}}

## See also

- [Dual Dedekind finite types](univalent-combinatorics.dual-dedekind-finite-types.md)
- [Finite types](univalent-combinatorics.finite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [Subfinite types](univalent-combinatorics.subfinite-types.md)
- [Subfinitely indexed types](univalent-combinatorics.subfinitely-indexed-types.md)

## References

{{#bibliography}} {{#reference Sto87}}

## External links

- [`Fin.Dedekind`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Dedekind.html)
  at TypeTopology
- [finite object#Dedekind finiteness](https://ncatlab.org/nlab/show/finite+object#dedekind_finiteness)
  at $n$Lab
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
