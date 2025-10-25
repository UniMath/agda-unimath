# The Cantor–Schröder–Bernstein–Escardó theorem

```agda
module foundation.cantor-schroder-bernstein-escardo where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cantor-schroder-bernstein-decidable-embeddings
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.propositional-maps
open import foundation-core.sets
```

</details>

## Idea

The classical Cantor–Schröder–Bernstein theorem asserts that from any pair of
[injective maps](foundation-core.injective-maps.md) `f : A → B` and `g : B → A`
we can construct a bijection between `A` and `B`. In a recent generalization,
Escardó proved that a Cantor–Schröder–Bernstein theorem also holds for
∞-groupoids. His generalization asserts that given two types that
[embed](foundation-core.embeddings.md) into each other, then the types are
[equivalent](foundation-core.equivalences.md). {{#cite Esc21}}

## Theorem

### The Cantor-Schröder-Bernstein-Escardó theorem

```agda
Cantor-Schröder-Bernstein-Escardó' :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-emb g → is-emb f → A ≃ B
Cantor-Schröder-Bernstein-Escardó' lem {f = f} {g} G F =
  Cantor-Schröder-Bernstein-WLPO'
    ( λ P → lem (Π-Prop ℕ (prop-Decidable-Prop ∘ P)))
    ( G , λ y → lem (fiber g y , is-prop-map-is-emb G y))
    ( F , λ y → lem (fiber f y , is-prop-map-is-emb F y))

Cantor-Schröder-Bernstein-Escardó :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} →
  A ↪ B → B ↪ A → A ≃ B
Cantor-Schröder-Bernstein-Escardó lem (f , F) (g , G) =
  Cantor-Schröder-Bernstein-Escardó' lem G F
```

### The Cantor–Schröder–Bernstein theorem

```agda
Cantor-Schröder-Bernstein :
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  (A : Set l1) (B : Set l2) →
  injection (type-Set A) (type-Set B) →
  injection (type-Set B) (type-Set A) →
  (type-Set A) ≃ (type-Set B)
Cantor-Schröder-Bernstein lem A B f g =
  Cantor-Schröder-Bernstein-Escardó lem (emb-injection B f) (emb-injection A g)
```

## References

- Escardó's formalizations of this theorem can be found at
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.index.html>.
  {{#cite TypeTopology}}

{{#bibliography}}

## See also

The Cantor–Schröder–Bernstein–Escardó theorem holds constructively for many
notions of finite type, including

- [Dedekind finite types](univalent-combinatorics.dedekind-finite-types.md)
- [Finite types](univalent-combinatorics.finite-types.md) (unformalized)
- [Finitely enumerable types](univalent-combinatorics.finitely-enumerable-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)
- [Subfinite types](univalent-combinatorics.subfinite-types.md)
- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)

See also the twin formalization in TypeTopology at
[`CantorSchroederBernstein.CSB-WLPO`](https://martinescardo.github.io/TypeTopology/CantorSchroederBernstein.CSB-WLPO.html).
There it is verified that the construction does not depend on any other axioms
than WLPO.

## External links

The Cantor–Schröder–Bernstein theorem is the 25th theorem on
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.
