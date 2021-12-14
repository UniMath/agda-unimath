# Agda formalisation of the Symmetry book [![build](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/SymmetryBookFormalization/actions/workflows/ci.yaml)

This repository is for a formalisation project in Agda of the symmetry book.

## The foundations folder

This folder contains the material of Chapter 2 and further concepts belonging to the univalent foundations of mathematics

## The the-circle folder

This folder contains the material of Chapter 3

## The groups folder

This folder contains the material of Chapter 4

## The subgroups folder

This folder contains the material of Chapter 5.

## Conventions

The naming convention in this library is such that the name of a construction closely matches the type of the construction. For example, the proof that the successor function on the integers is an equivalence has type `is-equiv succ-ℤ`. The name of the proof that the successor function on the integers is an equivalence is therefore `is-equiv-succ-ℤ`. Notice that most names are fully lowercase, and words are separated by hyphens. 

Names may also refer to types of the hypotheses used in the construction. Since the first objective of a name is to describe the type of the constructed term, the description of the hypotheses comes after the description of the conclusion in a name. For example, the term `is-equiv-is-contr-map` is a function of type `is-contr-map f → is-equiv f`, where `f` is a function already assumed. This convention has the advantage that if we have `H : is-contr-map f`, then the term `is-equiv-is-contr-map H` contains the description `is-contr-map` closest to the variable `H` of which it is a description.

1. The library uses Lisp style parentheses, and indent arguments of functions if they are on their own line.
2. Names are lowercase, with words split by hyphens
3. Names describe the object that is constructed first. For some theorems, the later part of a name contains descriptions of the hypotheses. 
4. The symbol for path concatenation is obtained by typing `\.`
