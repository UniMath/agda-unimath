# Peano arithmetic

```agda
module elementary-number-theory.peano-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.universe-levels
```

</details>

## Idea

## Axioms

We state the Peano axioms in type theory, using the
[identity type](foundation-core.identity-types.md) as equality, and prove that
they hold for the
[natural numbers `ℕ`](elementary-number-theory.natural-numbers.md).

### Peano's 1st axiom

There is an element **zero** of the natural numbers.

```agda
peano-axiom-1 : {l : Level} → UU l → UU l
peano-axiom-1 N = N

peano-1-ℕ : peano-axiom-1 ℕ
peano-1-ℕ = zero-ℕ
```

## Peano's 2nd axiom

The identity relation is reflexive on the natural numbers.

```agda
peano-axiom-2 : {l : Level} → UU l → UU l
peano-axiom-2 N = (x : N) → x ＝ x

peano-2-ℕ : peano-axiom-2 ℕ
peano-2-ℕ x = refl
```

### Peano's 3rd axiom

The identity relation on the natural numbers is symmetric.

```agda
peano-axiom-3 : {l : Level} → UU l → UU l
peano-axiom-3 N = (x y : N) → x ＝ y → y ＝ x

peano-3-ℕ : peano-axiom-3 ℕ
peano-3-ℕ x y = inv
```

### Peano's 4th axiom

The identity relation on the natural numbers is transitive.

```agda
peano-axiom-4 : {l : Level} → UU l → UU l
peano-axiom-4 N = (x y z : N) → y ＝ z → x ＝ y → x ＝ z

peano-4-ℕ : peano-axiom-4 ℕ
peano-4-ℕ x y z = concat' x
```

### Peano's 5th axiom

The 5th axiom of peano's arithmetic states that for every `a` and `b`, if
`a ＝ b` and `b` is a natural number, then `a` is a natural number. This axiom
does not make sense in type theory, as every element by definition live in a
specified type.

### Peano's 6th axiom

For every natural number, there is a **successor** natural number.

```agda
peano-axiom-6 : {l : Level} → UU l → UU l
peano-axiom-6 N = N → N

peano-6-ℕ : peano-axiom-6 ℕ
peano-6-ℕ = succ-ℕ
```

### Peano's 7th axiom

For two natural numbers `x` and `y`, if the successor of `x` is identified with
the successor of `y`, then `x` is identified with `y`.

```agda
peano-axiom-7 : {l : Level} (N : UU l) → peano-axiom-6 N → UU l
peano-axiom-7 N succ = (x y : N) → (x ＝ y) ↔ (succ x ＝ succ y)

peano-7-ℕ : peano-axiom-7 ℕ peano-6-ℕ
pr1 (peano-7-ℕ x y) refl = refl
pr2 (peano-7-ℕ x y) = is-injective-succ-ℕ
```

### Peano's 8th axiom

The zero natural number may not be identified with any successor natural number.

```agda
peano-axiom-8 :
  {l : Level} (N : UU l) → peano-axiom-1 N → peano-axiom-6 N → UU l
peano-axiom-8 N zero succ = (x : N) → succ x ≠ zero

peano-8-ℕ : peano-axiom-8 ℕ peano-1-ℕ peano-6-ℕ
peano-8-ℕ = is-nonzero-succ-ℕ
```

### Peano's 9th axiom

The natural numbers satisfy the following
[propositional](foundation-core.propositions.md) induction principle:

Given a predicate on the natural numbers `P : N → Prop`, then if

- `P zero` holds,

and

- if `P x` holds then `P (succ x)` holds,

then `P x` holds for all natural numbers `x`.

```agda
peano-axiom-9 :
  {l : Level} (N : UU l) → peano-axiom-1 N → peano-axiom-6 N → UU l
peano-axiom-9 N zero succ = (x : N) → succ x ≠ zero

peano-9-ℕ : peano-axiom-9 ℕ peano-1-ℕ peano-6-ℕ
peano-9-ℕ = ?
```

## References

## External links

- [Peano arithmetic](https://ncatlab.org/nlab/show/Peano+arithmetic) at nlab
- [Peano axioms](https://www.wikidata.org/wiki/Q842755) at Wikidata
- [Peano axioms](https://www.britannica.com/science/Peano-axioms) at Britannica
- [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms) at Wikipedia
- [Peano's Axioms](https://mathworld.wolfram.com/PeanosAxioms.html) at Wolfram
  Mathworld
