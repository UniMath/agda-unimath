# Peano arithmetic

```agda
module elementary-number-theory.peano-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels
open import elementary-number-theory.natural-numbers

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Axioms

### Peano's 1st axiom

There is an element **zero** of the natural numbers.

```agda
peano-1-axiom : {l : Level} → UU l → UU l
peano-1-axiom N = N

peano-1-ℕ : peano-1-axiom ℕ
peano-1-ℕ = zero-ℕ
```

## Peano's 2nd axiom

The identity relation is reflexive on the natural numbers.

```agda
peano-2-axiom : {l : Level} → UU l → UU l
peano-2-axiom N = (n : N) → n ＝ n

peano-2-ℕ : peano-2-axiom ℕ
peano-2-ℕ n = refl
```

### Peano's 3rd axiom

The identity relation on the natural numbers is symmetric.

```agda
peano-3-axiom : {l : Level} → UU l → UU l
peano-3-axiom N = (n m : N) → n ＝ m → m ＝ n

peano-3-ℕ : peano-3-axiom ℕ
peano-3-ℕ n m = inv
```

### Peano's 4th axiom

The identity relation on the natural numbers is transitive.

```agda
peano-4-axiom : {l : Level} → UU l → UU l
peano-4-axiom N = (n m r : N) → m ＝ r → n ＝ m → n ＝ r

peano-4-ℕ : peano-4-axiom ℕ
peano-4-ℕ n m r = concat' n
```

### Peano's 7th axiom

```agda
Peano-7 : (x y : ℕ) → (x ＝ y) ↔ (succ-ℕ x ＝ succ-ℕ y)
pr1 (Peano-7 x y) refl = refl
pr2 (Peano-7 x y) = is-injective-succ-ℕ
```

### Peano's 8th axiom

```agda
Peano-8 : (x : ℕ) → is-nonzero-ℕ (succ-ℕ x)
Peano-8 = is-nonzero-succ-ℕ
```

## External links

- [Peano arithmetic](https://ncatlab.org/nlab/show/Peano+arithmetic) at nlab
- [Peano axioms](https://www.wikidata.org/wiki/Q842755) at Wikidata
- [Peano axioms](https://www.britannica.com/science/Peano-axioms) at Britannica
- [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms) at Wikipedia
- [Peano's Axioms](https://mathworld.wolfram.com/PeanosAxioms.html) at Wolfram
  Mathworld
