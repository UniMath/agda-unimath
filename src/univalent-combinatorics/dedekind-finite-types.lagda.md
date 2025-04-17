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

{{#concept "Dedekind finite types" Agda=set-Dedekind-Finite-Type}} are types `X`
with the [property](foundation-core.propositions.md) that every
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

  is-equiv-map-cantor-schröder-bernstein-Dedekind-Finite-Type :
    is-equiv (map-emb f)
  is-equiv-map-cantor-schröder-bernstein-Dedekind-Finite-Type =
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

  cantor-schröder-bernstein-Dedekind-Finite-Type :
    type-Dedekind-Finite-Type X ≃ type-Dedekind-Finite-Type Y
  cantor-schröder-bernstein-Dedekind-Finite-Type =
    ( map-emb f , is-equiv-map-cantor-schröder-bernstein-Dedekind-Finite-Type)
```

### The subuniverse of propositions is Dedekind finite

> TODO

### Finite types are Dedekind finite

> TODO

### Subtypes of Dedekind finite types are Dedekind finite

> TODO

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

### Subfinitely indexed types are Dedekind finite

We reproduce a proof given by
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen) in this MathOverflow
answer: <https://mathoverflow.net/a/433318>.

**Proof.** Let $X$ be a subfinitely enumerated type, witnessed by
$Fin n ↩ D ↠ X$ where $h$ is the surjection. We wish to show $X$ is Dedekind
finite, so let $f : X ↪ X$ be an arbitrary embedding. Our goal is to prove $f$
is surjective.

Given an arbitrary $x : X$ we want to show there exists $z : X$ such that
$f(z) ＝ x$. Now, let $x_i = f^i(x)$. This defines an $ℕ$-indexed sequence of
elements of $X$. Each $x_i$ has a representative $x'_i : D$.

Now, by finite choice (i.e., if $h : D → X$ surjective then
$h ∘ - : D^{\operatorname{Fin}n} → X^{\operatorname{Fin}n}$ is also surjective.)
there is a sequence $x'_{-} :  D^{\operatorname{Fin}n}$ lifting
$x,f(x),…,f^{n-1}(x)$.

Now, the standard pigeonhole principle applies to $\operatorname{Fin}n$, so
there has to be $i < j$ in $\operatorname{Fin}n$ such that $x'_i = x'_j$, and in
particular $h(x'_i) = h(x'_j)$, i.e., $f^i(x) = f^j(x)$. By injectivity of $f$
we can cancel $i$ applications to obtain $x = f(f^{j-i-1}(x))$ so $f^{j-i-1}(x)$
is the desired preimage. ∎

> This remains to be formalized.

## Comments

It seems to be an open problem whether Dedekind finite types are closed under
coproducts or products. {{#cite Sto87}}

## See also

- [Finite types](univalent-combinatorics.finite-types.md)
- [Kuratowski finite sets](univalent-combinatorics.kuratowski-finite-sets.md)

## References

{{#bibliography}} {{#reference Sto87}}

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Dedekind`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Dedekind.html)
  at TypeTopology
- [finite object#Dedekind finiteness](https://ncatlab.org/nlab/show/finite+object#dedekind_finiteness)
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [Dedekind-infinite set](https://en.wikipedia.org/wiki/Dedekind-infinite_set)
  at Wikipedia
