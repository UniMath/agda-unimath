# Automorphisms

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.automorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.sets funext univalence
open import foundation.universe-levels

open import foundation-core.equivalences

open import structured-types.pointed-types
```

</details>

## Idea

An automorphism on a type `A` is an equivalence `A ≃ A`. We will just reuse the
infrastructure of equivalences for automorphisms.

## Definitions

### The type of automorphisms on a type

```agda
Aut : {l : Level} → UU l → UU l
Aut Y = Y ≃ Y

is-set-Aut : {l : Level} {A : UU l} → is-set A → is-set (Aut A)
is-set-Aut H = is-set-equiv-is-set H H

Aut-Set : {l : Level} → Set l → Set l
pr1 (Aut-Set A) = Aut (type-Set A)
pr2 (Aut-Set A) = is-set-Aut (is-set-type-Set A)

Aut-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (Aut-Pointed-Type A) = Aut A
pr2 (Aut-Pointed-Type A) = id-equiv
```
