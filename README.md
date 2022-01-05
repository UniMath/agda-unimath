# Agda formalisation of the Symmetry Book 

[![CI](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml/badge.svg)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml) [![pages-build-deployment](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/pages/pages-build-deployment/badge.svg)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/pages/pages-build-deployment)

This repository is for a formalisation project in Agda of the Symmetry Book.

## Members of the formalisation project 

Elisabeth Bonnevier, Pierre Cagne, Jonathan Prieto-Cubides, Egbert Rijke.

## Structure of the library

The Agda source of the library can be found in the folder `src`. This folder contains several subfolders:
1. The `foundations` folder contains the basics of dependent type theory. This part of the formalisation runs in `--safe` agda.
2. The `univalent-foundations` folder extends the type theory of Agda with function extensionality, propositional truncations, and the univalence axiom.
4. The `categories` folder contains some category theory.
6. The `the-circle` folder contains the material for Chapter 3.
7. The `synthetic-homotopy-theory` folder contains the formalisation of pullbacks, pushouts, and (eventually) homotopy groups of types.
8. The `groups` folder contains the material for Chapter 4 of the Symmetry book.
9. The `subgroups` folder contains the material for Chapter 5 of the Symmetry book. We plan to include quotient groups in this folder, and prove the isomorphism theorems.
10. The `order-theory` folder contains concepts of order theory.
11. The `univalent-combinatorics` folder contains further development of univalent mathematics of finite structures, and provides a source of examples of concrete groups.

This library is built on the formalisation of the [Introduction to Homotopy Type Theory](https://github.com/HoTT-Intro/Agda) book by Egbert Rijke.

Although the folders are roughly organised according to the chapters of the Symmetry Book, we don't commit to closely following the sectioning in the book.

The library is built in Agda 2.6.2. It can be compiled by running `make check` from the main folder.

## Conventions

1. The library uses Lisp style parentheses, and indent arguments of functions if they are on their own line.
2. If the arguments of a function don't fit on the same line (80 characters), put the arguments each on their own line below the function.
3. Extensive use of `where` in definitions seems to slow down agda, so we try to minimize its use.

### Names in the library

The naming convention in this library is such that the name of a construction closely matches the type of the construction. For example, the proof that the successor function on the integers is an equivalence has type `is-equiv succ-ℤ`. The name of the proof that the successor function on the integers is an equivalence is therefore `is-equiv-succ-ℤ`. Notice that most names are fully lowercase, and words are separated by hyphens. 

Names may also refer to types of the hypotheses used in the construction. Since the first objective of a name is to describe the type of the constructed term, the description of the hypotheses comes after the description of the conclusion in a name. For example, the term `is-equiv-is-contr-map` is a function of type `is-contr-map f → is-equiv f`, where `f` is a function already assumed. This convention has the advantage that if we have `H : is-contr-map f`, then the term `is-equiv-is-contr-map H` contains the description `is-contr-map` closest to the variable `H` of which it is a description.

1. Names are by default in lowercase, with words split by hyphens.
2. Important concepts can be capitalized. Usually, capitalized concepts form categories. Examples include `UU`, `Prop`, `Set`, `Semigroup`, `Monoid`, `Group`, `Preorder`, `Poset`, `Precat`, `Cat`.
3. Names describe the object that is constructed first. For some theorems, the later part of a name contains descriptions of the hypotheses. 
4. The symbol for path concatenation is obtained by typing `\.`

### Characterizing identity types

Identity types are characterized using `fundamental-theorem-id`, which can be found in `foundations.11-fundamental-theorem`. This theorem uses an implicit family `B` over a type `a`. The user must provide four arguments:

1. The base element `a:A`.
2. An element of type `B a`.
3. A proof that `Σ A B` is contractible.
4. A family of maps `(x : A) → Id a x → B x`.

The characterization of an identity type therefore revolves around the proof of contractibility of a total space. In order to give proofs of contractibility efficiently, the following theorems are often used:

1. `is-contr-equiv` and `is-contr-equiv'`. These are used to show that the asserted type is equivalent to a contractible type and therefore contractible. The `'` just switches the direction of the equivalence, so that it doesn't have to be manually inverted.
2. The structure identity principle `is-contr-total-Eq-structure`.
3. The substructure identity principle `is-contr-total-Eq-substructure`.
4. The identity principle for Π-types `is-contr-total-Eq-Π`.

A typical example is the characterization of the identity type of the type of equivalences:

```
  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  htpy-eq-equiv : {e e' : A ≃ B} (p : Id e e') → htpy-equiv e e'
  htpy-eq-equiv {e = e} {.e} refl =
    refl-htpy-equiv e

  abstract
    is-contr-total-htpy-equiv :
      (e : A ≃ B) → is-contr (Σ (A ≃ B) (λ e' → htpy-equiv e e'))
    is-contr-total-htpy-equiv (pair f is-equiv-f) =
      is-contr-total-Eq-substructure
        ( is-contr-total-htpy f)
        ( is-subtype-is-equiv)
        ( f)
        ( refl-htpy)
        ( is-equiv-f)

  is-equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → is-equiv (htpy-eq-equiv {e = e} {e'})
  is-equiv-htpy-eq-equiv e =
    fundamental-theorem-id e
      ( refl-htpy-equiv e)
      ( is-contr-total-htpy-equiv e)
      ( λ e' → htpy-eq-equiv {e = e} {e'})

  equiv-htpy-eq-equiv :
    (e e' : A ≃ B) → Id e e' ≃ (htpy-equiv e e')
  pr1 (equiv-htpy-eq-equiv e e') = htpy-eq-equiv
  pr2 (equiv-htpy-eq-equiv e e') = is-equiv-htpy-eq-equiv e e'

  eq-htpy-equiv : {e e' : A ≃ B} → ( htpy-equiv e e') → Id e e'
  eq-htpy-equiv {e = e} {e'} = map-inv-is-equiv (is-equiv-htpy-eq-equiv e e')
```
